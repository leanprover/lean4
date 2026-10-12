// Lean compiler output
// Module: Lean.Meta.Tactic.Lets
// Imports: public import Lean.Meta.Tactic.Replace public import Lean.Meta.LetToHave
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForallWithParamInfos(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedExprParamInfo_default;
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableBool___lam__0___boxed(lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_left(size_t, size_t);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withReverted___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_extractable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractable___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_ExtractLets_flushDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value),((lean_object*)&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_ExtractLets_flushDecls___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_flushDecls___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1_value;
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3_value;
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4_value;
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5_value;
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7_value),((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3_value),((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4_value),((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5_value)}};
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8_value),((lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6_value)}};
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ExtractLets_containsLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isLet___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ExtractLets_containsLet___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_containsLet___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "let expression expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateLetE!"};
static const lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.ExtractLets.extractCore"};
static const lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Meta.Tactic.Lets"};
static const lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_liftLets___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_liftLets___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "made no progress"};
static const lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_extractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extract_lets"};
static const lean_object* l_Lean_MVarId_extractLets___closed__0 = (const lean_object*)&l_Lean_MVarId_extractLets___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_extractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_extractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 33, 143, 120, 246, 234, 114, 64)}};
static const lean_object* l_Lean_MVarId_extractLets___closed__1 = (const lean_object*)&l_Lean_MVarId_extractLets___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unexpected auxiliary target"};
static const lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0 = (const lean_object*)&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0_value)}};
static const lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1 = (const lean_object*)&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2;
static lean_once_cell_t l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_liftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lift_lets"};
static const lean_object* l_Lean_MVarId_liftLets___closed__0 = (const lean_object*)&l_Lean_MVarId_liftLets___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_liftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_liftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 227, 82, 255, 128, 171, 101)}};
static const lean_object* l_Lean_MVarId_liftLets___closed__1 = (const lean_object*)&l_Lean_MVarId_liftLets___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_letToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let_to_have"};
static const lean_object* l_Lean_MVarId_letToHave___closed__0 = (const lean_object*)&l_Lean_MVarId_letToHave___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_letToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_letToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 121, 21, 93, 142, 174, 18, 85)}};
static const lean_object* l_Lean_MVarId_letToHave___closed__1 = (const lean_object*)&l_Lean_MVarId_letToHave___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_unsigned_to_nat(16u);
v___x_5_ = lean_mk_array(v___x_4_, v___x_3_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_obj_once(&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1, &l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = lean_obj_once(&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2, &l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2);
v___x_10_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_11_ = lean_box(0);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3, &l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_ExtractLets_instInhabitedState_default;
return v___x_14_;
}
}
lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg(lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_18_; uint8_t v_onlyGivenNames_19_; 
v___x_18_ = lean_st_ref_get(v_a_16_);
v_onlyGivenNames_19_ = lean_ctor_get_uint8(v_a_15_, 8);
if (v_onlyGivenNames_19_ == 0)
{
uint8_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v___x_18_);
v___x_20_ = 1;
v___x_21_ = lean_box(v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_givenNames_23_; uint8_t v___x_24_; 
v_givenNames_23_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_givenNames_23_);
lean_dec(v___x_18_);
v___x_24_ = l_List_isEmpty___redArg(v_givenNames_23_);
lean_dec(v_givenNames_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_box(v_onlyGivenNames_19_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
else
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = 0;
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_hasNextName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_15_ = stack[0].m_obj;
lean_object* v_a_16_ = stack[1].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_15_, v_a_16_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg___boxed(lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
return v_res_34_;
}
}
lean_object* l_Lean_Meta_ExtractLets_hasNextName(lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_35_, v_a_37_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_hasNextName_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_35_ = stack[0].m_obj;
lean_object* v_a_36_ = stack[1].m_obj;
lean_object* v_a_37_ = stack[2].m_obj;
lean_object* v_a_38_ = stack[3].m_obj;
lean_object* v_a_39_ = stack[4].m_obj;
lean_object* v_a_40_ = stack[5].m_obj;
lean_object* v_a_41_ = stack[6].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_Meta_ExtractLets_hasNextName(v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___boxed(lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_ExtractLets_hasNextName(v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
return v_res_53_;
}
}
lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg(lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_givenNames_63_; 
v___x_62_ = lean_st_ref_get(v_a_60_);
v_givenNames_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_givenNames_63_);
if (lean_obj_tag(v_givenNames_63_) == 0)
{
uint8_t v_onlyGivenNames_64_; 
lean_dec(v___x_62_);
v_onlyGivenNames_64_ = lean_ctor_get_uint8(v_a_59_, 8);
if (v_onlyGivenNames_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2));
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
else
{
lean_object* v_decls_69_; lean_object* v_valueMap_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_82_; 
v_decls_69_ = lean_ctor_get(v___x_62_, 1);
v_valueMap_70_ = lean_ctor_get(v___x_62_, 2);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v___x_62_, 0);
lean_dec(v_unused_83_);
v___x_72_ = v___x_62_;
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_valueMap_70_);
lean_inc(v_decls_69_);
lean_dec(v___x_62_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___x_77_; 
v_head_74_ = lean_ctor_get(v_givenNames_63_, 0);
lean_inc(v_head_74_);
v_tail_75_ = lean_ctor_get(v_givenNames_63_, 1);
lean_inc(v_tail_75_);
lean_dec_ref_known(v_givenNames_63_, 2);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v_tail_75_);
v___x_77_ = v___x_72_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_tail_75_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_decls_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_valueMap_70_);
v___x_77_ = v_reuseFailAlloc_81_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_st_ref_swap(v_a_60_, v___x_77_);
lean_dec(v___x_78_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_head_74_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_nextName_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_59_ = stack[0].m_obj;
lean_object* v_a_60_ = stack[1].m_obj;
lean_object* v_res_84_;
v_res_84_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_59_, v_a_60_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___boxed(lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_88_;
}
}
lean_object* l_Lean_Meta_ExtractLets_nextName_x3f(lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_89_, v_a_91_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_nextName_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_89_ = stack[0].m_obj;
lean_object* v_a_90_ = stack[1].m_obj;
lean_object* v_a_91_ = stack[2].m_obj;
lean_object* v_a_92_ = stack[3].m_obj;
lean_object* v_a_93_ = stack[4].m_obj;
lean_object* v_a_94_ = stack[5].m_obj;
lean_object* v_a_95_ = stack[6].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_Meta_ExtractLets_nextName_x3f(v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___boxed(lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Meta_ExtractLets_nextName_x3f(v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_107_;
}
}
lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(lean_object* v_binderName_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; lean_object* v_a_118_; 
v___x_117_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_112_, v_a_113_);
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
if (lean_obj_tag(v_a_118_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_169_; 
v_val_119_ = lean_ctor_get(v_a_118_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_a_118_);
if (v_isSharedCheck_169_ == 0)
{
v___x_121_ = v_a_118_;
v_isShared_122_ = v_isSharedCheck_169_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_dec(v_a_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_169_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1));
v___x_124_ = lean_name_eq(v_val_119_, v___x_123_);
if (v___x_124_ == 0)
{
lean_del_object(v___x_121_);
lean_dec(v_val_119_);
lean_dec(v_binderName_111_);
return v___x_117_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = l_Lean_Name_isAnonymous(v_binderName_111_);
if (v___x_125_ == 0)
{
uint8_t v_preserveBinderNames_126_; 
v_preserveBinderNames_126_ = lean_ctor_get_uint8(v_a_112_, 9);
if (v_preserveBinderNames_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = l_Lean_Name_hasMacroScopes(v_val_119_);
lean_dec(v_val_119_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_dec_ref(v___x_117_);
v___x_128_ = l_Lean_Core_mkFreshUserName(v_binderName_111_, v_a_114_, v_a_115_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_139_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_139_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_a_129_);
v___x_134_ = v___x_121_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_138_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_134_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_del_object(v___x_121_);
v_a_140_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_128_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_128_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_del_object(v___x_121_);
lean_dec(v_binderName_111_);
return v___x_117_;
}
}
else
{
lean_del_object(v___x_121_);
lean_dec(v_val_119_);
lean_dec(v_binderName_111_);
return v___x_117_;
}
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_val_119_);
lean_dec_ref(v___x_117_);
lean_dec(v_binderName_111_);
v___x_148_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1));
v___x_149_ = l_Lean_Core_mkFreshUserName(v___x_148_, v_a_114_, v_a_115_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_160_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_160_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_160_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_160_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_a_150_);
v___x_155_ = v___x_121_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_155_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
lean_del_object(v___x_121_);
v_a_161_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_149_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_149_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_177_; 
lean_dec(v_a_118_);
lean_dec(v_binderName_111_);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v___x_117_, 0);
lean_dec(v_unused_178_);
v___x_171_ = v___x_117_;
v_isShared_172_ = v_isSharedCheck_177_;
goto v_resetjp_170_;
}
else
{
lean_dec(v___x_117_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_177_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_box(0);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_111_ = stack[0].m_obj;
lean_object* v_a_112_ = stack[1].m_obj;
lean_object* v_a_113_ = stack[2].m_obj;
lean_object* v_a_114_ = stack[3].m_obj;
lean_object* v_a_115_ = stack[4].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___boxed(lean_object* v_binderName_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_186_;
}
}
lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(lean_object* v_binderName_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_187_, v_a_188_, v_a_190_, v_a_193_, v_a_194_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderName_187_ = stack[0].m_obj;
lean_object* v_a_188_ = stack[1].m_obj;
lean_object* v_a_189_ = stack[2].m_obj;
lean_object* v_a_190_ = stack[3].m_obj;
lean_object* v_a_191_ = stack[4].m_obj;
lean_object* v_a_192_ = stack[5].m_obj;
lean_object* v_a_193_ = stack[6].m_obj;
lean_object* v_a_194_ = stack[7].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(v_binderName_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___boxed(lean_object* v_binderName_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(v_binderName_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_207_;
}
}
uint8_t l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(lean_object* v_a_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
uint8_t v___x_210_; 
v___x_210_ = 0;
return v___x_210_;
}
else
{
lean_object* v_head_211_; lean_object* v_tail_212_; uint8_t v___x_213_; 
v_head_211_ = lean_ctor_get(v_x_209_, 0);
v_tail_212_ = lean_ctor_get(v_x_209_, 1);
v___x_213_ = lean_expr_eqv(v_a_208_, v_head_211_);
if (v___x_213_ == 0)
{
v_x_209_ = v_tail_212_;
goto _start;
}
else
{
return v___x_213_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_208_ = stack[0].m_obj;
lean_object* v_x_209_ = stack[1].m_obj;
uint8_t v_res_215_;
v_res_215_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v_a_208_, v_x_209_);
stack->m_num = v_res_215_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0___boxed(lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v_a_216_, v_x_217_);
lean_dec(v_x_217_);
lean_dec_ref(v_a_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(lean_object* v_fvars_220_, lean_object* v_e_221_){
_start:
{
uint8_t v___x_222_; lean_object* v_d_224_; lean_object* v_b_225_; 
v___x_222_ = l_Lean_Expr_hasFVar(v_e_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_e_221_);
return v___x_222_;
}
else
{
switch(lean_obj_tag(v_e_221_))
{
case 7:
{
lean_object* v_binderType_228_; lean_object* v_body_229_; 
v_binderType_228_ = lean_ctor_get(v_e_221_, 1);
lean_inc_ref(v_binderType_228_);
v_body_229_ = lean_ctor_get(v_e_221_, 2);
lean_inc_ref(v_body_229_);
lean_dec_ref_known(v_e_221_, 3);
v_d_224_ = v_binderType_228_;
v_b_225_ = v_body_229_;
goto v___jp_223_;
}
case 6:
{
lean_object* v_binderType_230_; lean_object* v_body_231_; 
v_binderType_230_ = lean_ctor_get(v_e_221_, 1);
lean_inc_ref(v_binderType_230_);
v_body_231_ = lean_ctor_get(v_e_221_, 2);
lean_inc_ref(v_body_231_);
lean_dec_ref_known(v_e_221_, 3);
v_d_224_ = v_binderType_230_;
v_b_225_ = v_body_231_;
goto v___jp_223_;
}
case 10:
{
lean_object* v_expr_232_; 
v_expr_232_ = lean_ctor_get(v_e_221_, 1);
lean_inc_ref(v_expr_232_);
lean_dec_ref_known(v_e_221_, 2);
v_e_221_ = v_expr_232_;
goto _start;
}
case 8:
{
lean_object* v_type_234_; lean_object* v_value_235_; lean_object* v_body_236_; uint8_t v___x_237_; 
v_type_234_ = lean_ctor_get(v_e_221_, 1);
lean_inc_ref(v_type_234_);
v_value_235_ = lean_ctor_get(v_e_221_, 2);
lean_inc_ref(v_value_235_);
v_body_236_ = lean_ctor_get(v_e_221_, 3);
lean_inc_ref(v_body_236_);
lean_dec_ref_known(v_e_221_, 4);
v___x_237_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_220_, v_type_234_);
if (v___x_237_ == 0)
{
uint8_t v___x_238_; 
v___x_238_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_220_, v_value_235_);
if (v___x_238_ == 0)
{
v_e_221_ = v_body_236_;
goto _start;
}
else
{
lean_dec_ref(v_body_236_);
return v___x_222_;
}
}
else
{
lean_dec_ref(v_body_236_);
lean_dec_ref(v_value_235_);
return v___x_222_;
}
}
case 5:
{
lean_object* v_fn_240_; lean_object* v_arg_241_; uint8_t v___x_242_; 
v_fn_240_ = lean_ctor_get(v_e_221_, 0);
lean_inc_ref(v_fn_240_);
v_arg_241_ = lean_ctor_get(v_e_221_, 1);
lean_inc_ref(v_arg_241_);
lean_dec_ref_known(v_e_221_, 2);
v___x_242_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_220_, v_fn_240_);
if (v___x_242_ == 0)
{
v_e_221_ = v_arg_241_;
goto _start;
}
else
{
lean_dec_ref(v_arg_241_);
return v___x_222_;
}
}
case 11:
{
lean_object* v_struct_244_; 
v_struct_244_ = lean_ctor_get(v_e_221_, 2);
lean_inc_ref(v_struct_244_);
lean_dec_ref_known(v_e_221_, 3);
v_e_221_ = v_struct_244_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_fvarId_246_ = lean_ctor_get(v_e_221_, 0);
lean_inc(v_fvarId_246_);
lean_dec_ref_known(v_e_221_, 1);
v___x_247_ = l_Lean_Expr_fvar___override(v_fvarId_246_);
v___x_248_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v___x_247_, v_fvars_220_);
lean_dec_ref(v___x_247_);
return v___x_248_;
}
default: 
{
uint8_t v___x_249_; 
lean_dec_ref(v_e_221_);
v___x_249_ = 0;
return v___x_249_;
}
}
}
v___jp_223_:
{
uint8_t v___x_226_; 
v___x_226_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_220_, v_d_224_);
if (v___x_226_ == 0)
{
v_e_221_ = v_b_225_;
goto _start;
}
else
{
lean_dec_ref(v_b_225_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_220_ = stack[0].m_obj;
lean_object* v_e_221_ = stack[1].m_obj;
uint8_t v_res_250_;
v_res_250_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_220_, v_e_221_);
stack->m_num = v_res_250_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1___boxed(lean_object* v_fvars_251_, lean_object* v_e_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_251_, v_e_252_);
lean_dec(v_fvars_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
uint8_t l_Lean_Meta_ExtractLets_extractable(lean_object* v_fvars_255_, lean_object* v_e_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_255_, v_e_256_);
if (v___x_257_ == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 1;
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractable_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_255_ = stack[0].m_obj;
lean_object* v_e_256_ = stack[1].m_obj;
uint8_t v_res_260_;
v_res_260_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_255_, v_e_256_);
stack->m_num = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractable___boxed(lean_object* v_fvars_261_, lean_object* v_e_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_261_, v_e_262_);
lean_dec(v_fvars_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg(lean_object* v_fvars_265_, lean_object* v_n_266_, lean_object* v_t_267_, lean_object* v_v_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___y_275_; lean_object* v___x_280_; lean_object* v_a_281_; uint8_t v___x_282_; 
v___x_280_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_269_, v_a_270_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v___x_280_);
v___x_282_ = lean_unbox(v_a_281_);
lean_dec(v_a_281_);
if (v___x_282_ == 0)
{
lean_dec_ref(v_v_268_);
lean_dec_ref(v_t_267_);
v___y_275_ = v_a_269_;
goto v___jp_274_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_265_, v_t_267_);
if (v___x_283_ == 0)
{
lean_dec_ref(v_v_268_);
v___y_275_ = v_a_269_;
goto v___jp_274_;
}
else
{
uint8_t v___x_284_; 
v___x_284_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_265_, v_v_268_);
if (v___x_284_ == 0)
{
v___y_275_ = v_a_269_;
goto v___jp_274_;
}
else
{
lean_object* v___x_285_; 
lean_inc(v_n_266_);
v___x_285_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_n_266_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_296_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
if (lean_obj_tag(v_a_286_) == 1)
{
lean_object* v_val_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_n_266_);
v_val_290_ = lean_ctor_get(v_a_286_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v_a_286_, 1);
v___x_291_ = lean_box(v___x_283_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_val_290_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_292_);
v___x_294_ = v___x_288_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_del_object(v___x_288_);
lean_dec(v_a_286_);
v___y_275_ = v_a_269_;
goto v___jp_274_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_n_266_);
v_a_297_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_285_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_285_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
v___jp_274_:
{
uint8_t v_lift_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_lift_276_ = lean_ctor_get_uint8(v___y_275_, 10);
v___x_277_ = lean_box(v_lift_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_n_266_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_isExtractableLet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_265_ = stack[0].m_obj;
lean_object* v_n_266_ = stack[1].m_obj;
lean_object* v_t_267_ = stack[2].m_obj;
lean_object* v_v_268_ = stack[3].m_obj;
lean_object* v_a_269_ = stack[4].m_obj;
lean_object* v_a_270_ = stack[5].m_obj;
lean_object* v_a_271_ = stack[6].m_obj;
lean_object* v_a_272_ = stack[7].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_265_, v_n_266_, v_t_267_, v_v_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg___boxed(lean_object* v_fvars_306_, lean_object* v_n_307_, lean_object* v_t_308_, lean_object* v_v_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_306_, v_n_307_, v_t_308_, v_v_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_fvars_306_);
return v_res_315_;
}
}
lean_object* l_Lean_Meta_ExtractLets_isExtractableLet(lean_object* v_fvars_316_, lean_object* v_n_317_, lean_object* v_t_318_, lean_object* v_v_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_316_, v_n_317_, v_t_318_, v_v_319_, v_a_320_, v_a_322_, v_a_325_, v_a_326_);
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_isExtractableLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_316_ = stack[0].m_obj;
lean_object* v_n_317_ = stack[1].m_obj;
lean_object* v_t_318_ = stack[2].m_obj;
lean_object* v_v_319_ = stack[3].m_obj;
lean_object* v_a_320_ = stack[4].m_obj;
lean_object* v_a_321_ = stack[5].m_obj;
lean_object* v_a_322_ = stack[6].m_obj;
lean_object* v_a_323_ = stack[7].m_obj;
lean_object* v_a_324_ = stack[8].m_obj;
lean_object* v_a_325_ = stack[9].m_obj;
lean_object* v_a_326_ = stack[10].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_Meta_ExtractLets_isExtractableLet(v_fvars_316_, v_n_317_, v_t_318_, v_v_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___boxed(lean_object* v_fvars_330_, lean_object* v_n_331_, lean_object* v_t_332_, lean_object* v_v_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_ExtractLets_isExtractableLet(v_fvars_330_, v_n_331_, v_t_332_, v_v_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_fvars_330_);
return v_res_342_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(lean_object* v_a_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
else
{
lean_object* v_key_346_; lean_object* v_tail_347_; uint8_t v___x_348_; 
v_key_346_ = lean_ctor_get(v_x_344_, 0);
v_tail_347_ = lean_ctor_get(v_x_344_, 2);
v___x_348_ = l_Lean_ExprStructEq_beq(v_key_346_, v_a_343_);
if (v___x_348_ == 0)
{
v_x_344_ = v_tail_347_;
goto _start;
}
else
{
return v___x_348_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_343_ = stack[0].m_obj;
lean_object* v_x_344_ = stack[1].m_obj;
uint8_t v_res_350_;
v_res_350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_343_, v_x_344_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_351_, lean_object* v_x_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_351_, v_x_352_);
lean_dec(v_x_352_);
lean_dec_ref(v_a_351_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(lean_object* v_a_355_, lean_object* v_b_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_dec(v_b_356_);
lean_dec_ref(v_a_355_);
return v_x_357_;
}
else
{
lean_object* v_key_358_; lean_object* v_value_359_; lean_object* v_tail_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_372_; 
v_key_358_ = lean_ctor_get(v_x_357_, 0);
v_value_359_ = lean_ctor_get(v_x_357_, 1);
v_tail_360_ = lean_ctor_get(v_x_357_, 2);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_372_ == 0)
{
v___x_362_ = v_x_357_;
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_tail_360_);
lean_inc(v_value_359_);
lean_inc(v_key_358_);
lean_dec(v_x_357_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_ExprStructEq_beq(v_key_358_, v_a_355_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_355_, v_b_356_, v_tail_360_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 2, v___x_365_);
v___x_367_ = v___x_362_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_key_358_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_value_359_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
else
{
lean_object* v___x_370_; 
lean_dec(v_value_359_);
lean_dec(v_key_358_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_b_356_);
lean_ctor_set(v___x_362_, 0, v_a_355_);
v___x_370_ = v___x_362_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_355_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_b_356_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_tail_360_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
return v_x_373_;
}
else
{
lean_object* v_key_375_; lean_object* v_value_376_; lean_object* v_tail_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_400_; 
v_key_375_ = lean_ctor_get(v_x_374_, 0);
v_value_376_ = lean_ctor_get(v_x_374_, 1);
v_tail_377_ = lean_ctor_get(v_x_374_, 2);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_400_ == 0)
{
v___x_379_ = v_x_374_;
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_tail_377_);
lean_inc(v_value_376_);
lean_inc(v_key_375_);
lean_dec(v_x_374_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v_fold_385_; uint64_t v___x_386_; uint64_t v___x_387_; uint64_t v___x_388_; size_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_381_ = lean_array_get_size(v_x_373_);
v___x_382_ = l_Lean_ExprStructEq_hash(v_key_375_);
v___x_383_ = 32ULL;
v___x_384_ = lean_uint64_shift_right(v___x_382_, v___x_383_);
v_fold_385_ = lean_uint64_xor(v___x_382_, v___x_384_);
v___x_386_ = 16ULL;
v___x_387_ = lean_uint64_shift_right(v_fold_385_, v___x_386_);
v___x_388_ = lean_uint64_xor(v_fold_385_, v___x_387_);
v___x_389_ = lean_uint64_to_usize(v___x_388_);
v___x_390_ = lean_usize_of_nat(v___x_381_);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_sub(v___x_390_, v___x_391_);
v___x_393_ = lean_usize_land(v___x_389_, v___x_392_);
v___x_394_ = lean_array_uget_borrowed(v_x_373_, v___x_393_);
lean_inc(v___x_394_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 2, v___x_394_);
v___x_396_ = v___x_379_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_key_375_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_value_376_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___x_394_);
v___x_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = lean_array_uset(v_x_373_, v___x_393_, v___x_396_);
v_x_373_ = v___x_397_;
v_x_374_ = v_tail_377_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(lean_object* v_i_401_, lean_object* v_source_402_, lean_object* v_target_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_array_get_size(v_source_402_);
v___x_405_ = lean_nat_dec_lt(v_i_401_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec_ref(v_source_402_);
lean_dec(v_i_401_);
return v_target_403_;
}
else
{
lean_object* v_es_406_; lean_object* v___x_407_; lean_object* v_source_408_; lean_object* v_target_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_es_406_ = lean_array_fget(v_source_402_, v_i_401_);
v___x_407_ = lean_box(0);
v_source_408_ = lean_array_fset(v_source_402_, v_i_401_, v___x_407_);
v_target_409_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(v_target_403_, v_es_406_);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_i_401_, v___x_410_);
lean_dec(v_i_401_);
v_i_401_ = v___x_411_;
v_source_402_ = v_source_408_;
v_target_403_ = v_target_409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(lean_object* v_data_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_nbuckets_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_414_ = lean_array_get_size(v_data_413_);
v___x_415_ = lean_unsigned_to_nat(2u);
v_nbuckets_416_ = lean_nat_mul(v___x_414_, v___x_415_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_box(0);
v___x_419_ = lean_mk_array(v_nbuckets_416_, v___x_418_);
v___x_420_ = lean_array_propagate_mark(v_data_413_, v___x_419_);
v___x_421_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v___x_417_, v_data_413_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_b_424_){
_start:
{
lean_object* v_size_425_; lean_object* v_buckets_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_469_; 
v_size_425_ = lean_ctor_get(v_m_422_, 0);
v_buckets_426_ = lean_ctor_get(v_m_422_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_m_422_);
if (v_isSharedCheck_469_ == 0)
{
v___x_428_ = v_m_422_;
v_isShared_429_ = v_isSharedCheck_469_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_buckets_426_);
lean_inc(v_size_425_);
lean_dec(v_m_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_469_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v_fold_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v_bkt_443_; uint8_t v___x_444_; 
v___x_430_ = lean_array_get_size(v_buckets_426_);
v___x_431_ = l_Lean_ExprStructEq_hash(v_a_423_);
v___x_432_ = 32ULL;
v___x_433_ = lean_uint64_shift_right(v___x_431_, v___x_432_);
v_fold_434_ = lean_uint64_xor(v___x_431_, v___x_433_);
v___x_435_ = 16ULL;
v___x_436_ = lean_uint64_shift_right(v_fold_434_, v___x_435_);
v___x_437_ = lean_uint64_xor(v_fold_434_, v___x_436_);
v___x_438_ = lean_uint64_to_usize(v___x_437_);
v___x_439_ = lean_usize_of_nat(v___x_430_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_sub(v___x_439_, v___x_440_);
v___x_442_ = lean_usize_land(v___x_438_, v___x_441_);
v_bkt_443_ = lean_array_uget_borrowed(v_buckets_426_, v___x_442_);
v___x_444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_423_, v_bkt_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v_size_x27_446_; lean_object* v___x_447_; lean_object* v_buckets_x27_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v_size_x27_446_ = lean_nat_add(v_size_425_, v___x_445_);
lean_dec(v_size_425_);
lean_inc(v_bkt_443_);
v___x_447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_447_, 0, v_a_423_);
lean_ctor_set(v___x_447_, 1, v_b_424_);
lean_ctor_set(v___x_447_, 2, v_bkt_443_);
v_buckets_x27_448_ = lean_array_uset(v_buckets_426_, v___x_442_, v___x_447_);
v___x_449_ = lean_unsigned_to_nat(4u);
v___x_450_ = lean_nat_mul(v_size_x27_446_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = lean_nat_div(v___x_450_, v___x_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_array_get_size(v_buckets_x27_448_);
v___x_454_ = lean_nat_dec_le(v___x_452_, v___x_453_);
lean_dec(v___x_452_);
if (v___x_454_ == 0)
{
lean_object* v_val_455_; lean_object* v___x_457_; 
v_val_455_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_buckets_x27_448_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v_val_455_);
lean_ctor_set(v___x_428_, 0, v_size_x27_446_);
v___x_457_ = v___x_428_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_size_x27_446_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_val_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
else
{
lean_object* v___x_460_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v_buckets_x27_448_);
lean_ctor_set(v___x_428_, 0, v_size_x27_446_);
v___x_460_ = v___x_428_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_size_x27_446_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_buckets_x27_448_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
else
{
lean_object* v___x_462_; lean_object* v_buckets_x27_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
lean_inc(v_bkt_443_);
v___x_462_ = lean_box(0);
v_buckets_x27_463_ = lean_array_uset(v_buckets_426_, v___x_442_, v___x_462_);
v___x_464_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_423_, v_b_424_, v_bkt_443_);
v___x_465_ = lean_array_uset(v_buckets_x27_463_, v___x_442_, v___x_464_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_465_);
v___x_467_ = v___x_428_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_size_425_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg(lean_object* v_decl_470_, uint8_t v_isLet_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_475_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v_givenNames_481_; lean_object* v_decls_482_; lean_object* v_valueMap_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_501_; 
v___x_475_ = lean_st_ref_take(v_a_473_);
v_givenNames_481_ = lean_ctor_get(v___x_475_, 0);
v_decls_482_ = lean_ctor_get(v___x_475_, 1);
v_valueMap_483_ = lean_ctor_get(v___x_475_, 2);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_501_ == 0)
{
v___x_485_ = v___x_475_;
v_isShared_486_ = v_isSharedCheck_501_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_valueMap_483_);
lean_inc(v_decls_482_);
lean_inc(v_givenNames_481_);
lean_dec(v___x_475_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_501_;
goto v_resetjp_484_;
}
v___jp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_st_ref_put(v_a_473_, v_snd_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v_fst_477_);
return v___x_480_;
}
v_resetjp_484_:
{
uint8_t v_merge_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_merge_487_ = lean_ctor_get_uint8(v_a_472_, 6);
v___x_488_ = lean_box(0);
lean_inc_ref(v_decl_470_);
v___x_489_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_489_, 0, v_decl_470_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*1, v_isLet_471_);
v___x_490_ = lean_array_push(v_decls_482_, v___x_489_);
if (v_merge_487_ == 0)
{
lean_object* v___x_492_; 
lean_dec_ref(v_decl_470_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_490_);
v___x_492_ = v___x_485_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_givenNames_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_valueMap_483_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v_fst_477_ = v___x_488_;
v_snd_478_ = v___x_492_;
goto v___jp_476_;
}
}
else
{
uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_494_ = 0;
v___x_495_ = l_Lean_LocalDecl_value(v_decl_470_, v___x_494_);
v___x_496_ = l_Lean_LocalDecl_fvarId(v_decl_470_);
lean_dec_ref(v_decl_470_);
v___x_497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_483_, v___x_495_, v___x_496_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 2, v___x_497_);
lean_ctor_set(v___x_485_, 1, v___x_490_);
v___x_499_ = v___x_485_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_givenNames_481_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
v_fst_477_ = v___x_488_;
v_snd_478_ = v___x_499_;
goto v___jp_476_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_addDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_470_ = stack[0].m_obj;
uint8_t v_isLet_471_ = stack[1].m_num;
lean_object* v_a_472_ = stack[2].m_obj;
lean_object* v_a_473_ = stack[3].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_470_, v_isLet_471_, v_a_472_, v_a_473_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg___boxed(lean_object* v_decl_503_, lean_object* v_isLet_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
uint8_t v_isLet_boxed_508_; lean_object* v_res_509_; 
v_isLet_boxed_508_ = lean_unbox(v_isLet_504_);
v_res_509_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_503_, v_isLet_boxed_508_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_509_;
}
}
lean_object* l_Lean_Meta_ExtractLets_addDecl(lean_object* v_decl_510_, uint8_t v_isLet_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_510_, v_isLet_511_, v_a_512_, v_a_514_);
return v___x_520_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_addDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_510_ = stack[0].m_obj;
uint8_t v_isLet_511_ = stack[1].m_num;
lean_object* v_a_512_ = stack[2].m_obj;
lean_object* v_a_513_ = stack[3].m_obj;
lean_object* v_a_514_ = stack[4].m_obj;
lean_object* v_a_515_ = stack[5].m_obj;
lean_object* v_a_516_ = stack[6].m_obj;
lean_object* v_a_517_ = stack[7].m_obj;
lean_object* v_a_518_ = stack[8].m_obj;
lean_object* v_res_521_;
v_res_521_ = l_Lean_Meta_ExtractLets_addDecl(v_decl_510_, v_isLet_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___boxed(lean_object* v_decl_522_, lean_object* v_isLet_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
uint8_t v_isLet_boxed_532_; lean_object* v_res_533_; 
v_isLet_boxed_532_ = lean_unbox(v_isLet_523_);
v_res_533_ = l_Lean_Meta_ExtractLets_addDecl(v_decl_522_, v_isLet_boxed_532_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0(lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_m_535_, v_a_536_, v_b_537_);
return v___x_538_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_x_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_540_ = stack[1].m_obj;
lean_object* v_x_541_ = stack[2].m_obj;
uint8_t v_res_543_;
v_res_543_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(lean_box(0), v_a_540_, v_x_541_);
stack->m_num = v_res_543_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_544_, lean_object* v_a_545_, lean_object* v_x_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(v_00_u03b2_544_, v_a_545_, v_x_546_);
lean_dec(v_x_546_);
lean_dec_ref(v_a_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1(lean_object* v_00_u03b2_549_, lean_object* v_data_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_data_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2(lean_object* v_00_u03b2_552_, lean_object* v_a_553_, lean_object* v_b_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_553_, v_b_554_, v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_557_, lean_object* v_i_558_, lean_object* v_source_559_, lean_object* v_target_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v_i_558_, v_source_559_, v_target_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(v_x_563_, v_x_564_);
return v___x_565_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(lean_object* v_k_566_, lean_object* v_t_567_){
_start:
{
if (lean_obj_tag(v_t_567_) == 0)
{
lean_object* v_k_568_; lean_object* v_l_569_; lean_object* v_r_570_; uint8_t v___x_571_; 
v_k_568_ = lean_ctor_get(v_t_567_, 1);
v_l_569_ = lean_ctor_get(v_t_567_, 3);
v_r_570_ = lean_ctor_get(v_t_567_, 4);
v___x_571_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_566_, v_k_568_);
switch(v___x_571_)
{
case 0:
{
v_t_567_ = v_l_569_;
goto _start;
}
case 1:
{
uint8_t v___x_573_; 
v___x_573_ = 1;
return v___x_573_;
}
default: 
{
v_t_567_ = v_r_570_;
goto _start;
}
}
}
else
{
uint8_t v___x_575_; 
v___x_575_ = 0;
return v___x_575_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_566_ = stack[0].m_obj;
lean_object* v_t_567_ = stack[1].m_obj;
uint8_t v_res_576_;
v_res_576_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_566_, v_t_567_);
stack->m_num = v_res_576_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg___boxed(lean_object* v_k_577_, lean_object* v_t_578_){
_start:
{
uint8_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_577_, v_t_578_);
lean_dec(v_t_578_);
lean_dec(v_k_577_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(lean_object* v___x_581_, lean_object* v_e_582_){
_start:
{
uint8_t v___x_583_; lean_object* v_d_585_; lean_object* v_b_586_; 
v___x_583_ = l_Lean_Expr_hasFVar(v_e_582_);
if (v___x_583_ == 0)
{
return v___x_583_;
}
else
{
switch(lean_obj_tag(v_e_582_))
{
case 7:
{
lean_object* v_binderType_589_; lean_object* v_body_590_; 
v_binderType_589_ = lean_ctor_get(v_e_582_, 1);
v_body_590_ = lean_ctor_get(v_e_582_, 2);
v_d_585_ = v_binderType_589_;
v_b_586_ = v_body_590_;
goto v___jp_584_;
}
case 6:
{
lean_object* v_binderType_591_; lean_object* v_body_592_; 
v_binderType_591_ = lean_ctor_get(v_e_582_, 1);
v_body_592_ = lean_ctor_get(v_e_582_, 2);
v_d_585_ = v_binderType_591_;
v_b_586_ = v_body_592_;
goto v___jp_584_;
}
case 10:
{
lean_object* v_expr_593_; 
v_expr_593_ = lean_ctor_get(v_e_582_, 1);
v_e_582_ = v_expr_593_;
goto _start;
}
case 8:
{
lean_object* v_type_595_; lean_object* v_value_596_; lean_object* v_body_597_; uint8_t v___x_598_; 
v_type_595_ = lean_ctor_get(v_e_582_, 1);
v_value_596_ = lean_ctor_get(v_e_582_, 2);
v_body_597_ = lean_ctor_get(v_e_582_, 3);
v___x_598_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_581_, v_type_595_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
v___x_599_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_581_, v_value_596_);
if (v___x_599_ == 0)
{
v_e_582_ = v_body_597_;
goto _start;
}
else
{
return v___x_583_;
}
}
else
{
return v___x_583_;
}
}
case 5:
{
lean_object* v_fn_601_; lean_object* v_arg_602_; uint8_t v___x_603_; 
v_fn_601_ = lean_ctor_get(v_e_582_, 0);
v_arg_602_ = lean_ctor_get(v_e_582_, 1);
v___x_603_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_581_, v_fn_601_);
if (v___x_603_ == 0)
{
v_e_582_ = v_arg_602_;
goto _start;
}
else
{
return v___x_583_;
}
}
case 11:
{
lean_object* v_struct_605_; 
v_struct_605_ = lean_ctor_get(v_e_582_, 2);
v_e_582_ = v_struct_605_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_607_; uint8_t v___x_608_; 
v_fvarId_607_ = lean_ctor_get(v_e_582_, 0);
v___x_608_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_fvarId_607_, v___x_581_);
return v___x_608_;
}
default: 
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
}
}
v___jp_584_:
{
uint8_t v___x_587_; 
v___x_587_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_581_, v_d_585_);
if (v___x_587_ == 0)
{
v_e_582_ = v_b_586_;
goto _start;
}
else
{
return v___x_583_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_581_ = stack[0].m_obj;
lean_object* v_e_582_ = stack[1].m_obj;
uint8_t v_res_610_;
v_res_610_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_581_, v_e_582_);
stack->m_num = v_res_610_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1___boxed(lean_object* v___x_611_, lean_object* v_e_612_){
_start:
{
uint8_t v_res_613_; lean_object* v_r_614_; 
v_res_613_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_611_, v_e_612_);
lean_dec_ref(v_e_612_);
lean_dec(v___x_611_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(lean_object* v_as_615_, size_t v_sz_616_, size_t v_i_617_, lean_object* v_b_618_){
_start:
{
lean_object* v_a_621_; uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_lt(v_i_617_, v_sz_616_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_b_618_);
return v___x_626_;
}
else
{
lean_object* v_snd_627_; lean_object* v_fst_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_662_; 
v_snd_627_ = lean_ctor_get(v_b_618_, 1);
v_fst_628_ = lean_ctor_get(v_b_618_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_b_618_);
if (v_isSharedCheck_662_ == 0)
{
v___x_630_ = v_b_618_;
v_isShared_631_ = v_isSharedCheck_662_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_627_);
lean_inc(v_fst_628_);
lean_dec(v_b_618_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_662_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_661_; 
v_fst_632_ = lean_ctor_get(v_snd_627_, 0);
v_snd_633_ = lean_ctor_get(v_snd_627_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_snd_627_);
if (v_isSharedCheck_661_ == 0)
{
v___x_635_ = v_snd_627_;
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_inc(v_fst_632_);
lean_dec(v_snd_627_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_a_637_; lean_object* v_decl_638_; uint8_t v___y_640_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_a_637_ = lean_array_uget_borrowed(v_as_615_, v_i_617_);
v_decl_638_ = lean_ctor_get(v_a_637_, 0);
v___x_657_ = l_Lean_LocalDecl_type(v_decl_638_);
v___x_658_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_628_, v___x_657_);
lean_dec_ref(v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = l_Lean_LocalDecl_value(v_decl_638_, v___x_658_);
v___x_660_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_628_, v___x_659_);
lean_dec_ref(v___x_659_);
v___y_640_ = v___x_660_;
goto v___jp_639_;
}
else
{
v___y_640_ = v___x_658_;
goto v___jp_639_;
}
v___jp_639_:
{
if (v___y_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_inc(v_a_637_);
v___x_641_ = lean_array_push(v_fst_632_, v_a_637_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_641_);
v___x_643_ = v___x_635_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_snd_633_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_643_);
v___x_645_ = v___x_630_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_fst_628_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v_a_621_ = v___x_645_;
goto v___jp_620_;
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
lean_inc(v_a_637_);
v___x_648_ = lean_array_push(v_snd_633_, v_a_637_);
v___x_649_ = l_Lean_LocalDecl_fvarId(v_decl_638_);
v___x_650_ = l_Lean_FVarIdSet_insert(v_fst_628_, v___x_649_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_648_);
v___x_652_ = v___x_635_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_fst_632_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_648_);
v___x_652_ = v_reuseFailAlloc_656_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_652_);
lean_ctor_set(v___x_630_, 0, v___x_650_);
v___x_654_ = v___x_630_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
v_a_621_ = v___x_654_;
goto v___jp_620_;
}
}
}
}
}
}
}
v___jp_620_:
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_617_, v___x_622_);
v_i_617_ = v___x_623_;
v_b_618_ = v_a_621_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_615_ = stack[0].m_obj;
size_t v_sz_616_ = stack[1].m_num;
size_t v_i_617_ = stack[2].m_num;
lean_object* v_b_618_ = stack[3].m_obj;
lean_object* v_res_663_;
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_615_, v_sz_616_, v_i_617_, v_b_618_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(lean_object* v_as_664_, lean_object* v_sz_665_, lean_object* v_i_666_, lean_object* v_b_667_, lean_object* v___y_668_){
_start:
{
size_t v_sz_boxed_669_; size_t v_i_boxed_670_; lean_object* v_res_671_; 
v_sz_boxed_669_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_670_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_664_, v_sz_boxed_669_, v_i_boxed_670_, v_b_667_);
lean_dec_ref(v_as_664_);
return v_res_671_;
}
}
lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object* v_fvar_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_fvarSet_683_; lean_object* v_fvarSet_684_; lean_object* v___x_685_; lean_object* v_decls_686_; lean_object* v___x_687_; lean_object* v___x_688_; size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; 
v_fvarSet_683_ = lean_box(1);
v_fvarSet_684_ = l_Lean_FVarIdSet_insert(v_fvarSet_683_, v_fvar_674_);
v___x_685_ = lean_st_ref_get(v_a_677_);
v_decls_686_ = lean_ctor_get(v___x_685_, 1);
lean_inc_ref(v_decls_686_);
lean_dec(v___x_685_);
v___x_687_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_fvarSet_684_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v_sz_689_ = lean_array_size(v_decls_686_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_decls_686_, v_sz_689_, v___x_690_, v___x_688_);
lean_dec_ref(v_decls_686_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_714_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_714_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_714_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_714_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_snd_696_; lean_object* v_fst_697_; lean_object* v_snd_698_; lean_object* v___x_699_; lean_object* v_givenNames_700_; lean_object* v_valueMap_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_712_; 
v_snd_696_ = lean_ctor_get(v_a_692_, 1);
lean_inc(v_snd_696_);
lean_dec(v_a_692_);
v_fst_697_ = lean_ctor_get(v_snd_696_, 0);
lean_inc(v_fst_697_);
v_snd_698_ = lean_ctor_get(v_snd_696_, 1);
lean_inc(v_snd_698_);
lean_dec(v_snd_696_);
v___x_699_ = lean_st_ref_take(v_a_677_);
v_givenNames_700_ = lean_ctor_get(v___x_699_, 0);
v_valueMap_701_ = lean_ctor_get(v___x_699_, 2);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_699_, 1);
lean_dec(v_unused_713_);
v___x_703_ = v___x_699_;
v_isShared_704_ = v_isSharedCheck_712_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_valueMap_701_);
lean_inc(v_givenNames_700_);
lean_dec(v___x_699_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_712_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_fst_697_);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_givenNames_700_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_fst_697_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_valueMap_701_);
v___x_706_ = v_reuseFailAlloc_711_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_st_ref_put(v_a_677_, v___x_706_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_snd_698_);
v___x_709_ = v___x_694_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_snd_698_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_691_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_691_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_flushDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvar_674_ = stack[0].m_obj;
lean_object* v_a_675_ = stack[1].m_obj;
lean_object* v_a_676_ = stack[2].m_obj;
lean_object* v_a_677_ = stack[3].m_obj;
lean_object* v_a_678_ = stack[4].m_obj;
lean_object* v_a_679_ = stack[5].m_obj;
lean_object* v_a_680_ = stack[6].m_obj;
lean_object* v_a_681_ = stack[7].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Lean_Meta_ExtractLets_flushDecls(v_fvar_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object* v_fvar_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_ExtractLets_flushDecls(v_fvar_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
return v_res_733_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object* v_00_u03b2_734_, lean_object* v_k_735_, lean_object* v_t_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_735_, v_t_736_);
return v___x_737_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_735_ = stack[1].m_obj;
lean_object* v_t_736_ = stack[2].m_obj;
uint8_t v_res_738_;
v_res_738_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_box(0), v_k_735_, v_t_736_);
stack->m_num = v_res_738_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object* v_00_u03b2_739_, lean_object* v_k_740_, lean_object* v_t_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(v_00_u03b2_739_, v_k_740_, v_t_741_);
lean_dec(v_t_741_);
lean_dec(v_k_740_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object* v_as_744_, size_t v_sz_745_, size_t v_i_746_, lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_744_, v_sz_745_, v_i_746_, v_b_747_);
return v___x_756_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_744_ = stack[0].m_obj;
size_t v_sz_745_ = stack[1].m_num;
size_t v_i_746_ = stack[2].m_num;
lean_object* v_b_747_ = stack[3].m_obj;
lean_object* v___y_748_ = stack[4].m_obj;
lean_object* v___y_749_ = stack[5].m_obj;
lean_object* v___y_750_ = stack[6].m_obj;
lean_object* v___y_751_ = stack[7].m_obj;
lean_object* v___y_752_ = stack[8].m_obj;
lean_object* v___y_753_ = stack[9].m_obj;
lean_object* v___y_754_ = stack[10].m_obj;
lean_object* v_res_757_;
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_744_, v_sz_745_, v_i_746_, v_b_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object* v_as_758_, lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_771_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_758_, v_sz_boxed_770_, v_i_boxed_771_, v_b_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_as_758_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object* v_x_773_){
_start:
{
lean_object* v_decl_774_; 
v_decl_774_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_decl_774_);
return v_decl_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object* v_x_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(v_x_775_);
lean_dec_ref(v_x_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object* v_lctx_777_, lean_object* v_x1_778_, lean_object* v_x2_779_){
_start:
{
lean_object* v_decl_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_decl_780_ = lean_ctor_get(v_x2_779_, 0);
v___x_781_ = l_Lean_LocalDecl_fvarId(v_decl_780_);
v___x_782_ = l_Lean_LocalContext_contains(v_lctx_777_, v___x_781_);
lean_dec(v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
v___x_783_ = lean_array_push(v_x1_778_, v_x2_779_);
return v___x_783_;
}
else
{
lean_dec_ref(v_x2_779_);
return v_x1_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object* v_lctx_784_, lean_object* v_x1_785_, lean_object* v_x2_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(v_lctx_784_, v_x1_785_, v_x2_786_);
lean_dec_ref(v_lctx_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_k_810_, lean_object* v_decls_811_, lean_object* v_lctx_812_){
_start:
{
lean_object* v___y_814_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_array_get_size(v_decls_811_);
v___x_823_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_824_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_825_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
if (v___x_825_ == 0)
{
lean_dec_ref(v_lctx_812_);
lean_dec_ref(v_decls_811_);
v___y_814_ = v___x_823_;
goto v___jp_813_;
}
else
{
lean_object* v___f_826_; uint8_t v___x_827_; 
v___f_826_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_826_, 0, v_lctx_812_);
v___x_827_ = lean_nat_dec_le(v___x_822_, v___x_822_);
if (v___x_827_ == 0)
{
if (v___x_825_ == 0)
{
lean_dec_ref(v___f_826_);
lean_dec_ref(v_decls_811_);
v___y_814_ = v___x_823_;
goto v___jp_813_;
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((size_t)0ULL);
v___x_829_ = lean_usize_of_nat(v___x_822_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_824_, v___f_826_, v_decls_811_, v___x_828_, v___x_829_, v___x_823_);
v___y_814_ = v___x_830_;
goto v___jp_813_;
}
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_822_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_824_, v___f_826_, v_decls_811_, v___x_831_, v___x_832_, v___x_823_);
v___y_814_ = v___x_833_;
goto v___jp_813_;
}
}
v___jp_813_:
{
lean_object* v___x_815_; size_t v_sz_816_; size_t v___x_817_; lean_object* v_decls_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_815_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_816_ = lean_array_size(v___y_814_);
v___x_817_ = ((size_t)0ULL);
v_decls_818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_815_, v___f_807_, v_sz_816_, v___x_817_, v___y_814_);
v___x_819_ = lean_array_to_list(v_decls_818_);
v___x_820_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_808_, v_inst_809_, v___x_819_, v_k_810_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_decls_838_, lean_object* v_k_839_){
_start:
{
lean_object* v_toBind_840_; lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___x_843_; 
v_toBind_840_ = lean_ctor_get(v_inst_835_, 1);
lean_inc(v_toBind_840_);
v___f_841_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_842_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_842_, 0, v___f_841_);
lean_closure_set(v___f_842_, 1, v_inst_836_);
lean_closure_set(v___f_842_, 2, v_inst_835_);
lean_closure_set(v___f_842_, 3, v_k_839_);
lean_closure_set(v___f_842_, 4, v_decls_838_);
v___x_843_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v_inst_837_, v___f_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_844_, lean_object* v_00_u03b1_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_decls_849_, lean_object* v_k_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_846_, v_inst_847_, v_inst_848_, v_decls_849_, v_k_850_);
return v___x_851_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_852_, size_t v_i_853_, size_t v_stop_854_, lean_object* v_b_855_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_eq(v_i_853_, v_stop_854_);
if (v___x_856_ == 0)
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; lean_object* v_decl_860_; uint8_t v_isLet_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_sub(v_i_853_, v___x_857_);
v___x_859_ = lean_array_uget_borrowed(v_as_852_, v___x_858_);
v_decl_860_ = lean_ctor_get(v___x_859_, 0);
v_isLet_861_ = lean_ctor_get_uint8(v___x_859_, sizeof(void*)*1);
v___x_862_ = l_Lean_LocalDecl_userName(v_decl_860_);
v___x_863_ = l_Lean_LocalDecl_type(v_decl_860_);
v___x_864_ = l_Lean_LocalDecl_value(v_decl_860_, v___x_856_);
lean_inc_ref(v_decl_860_);
v___x_865_ = l_Lean_LocalDecl_toExpr(v_decl_860_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_mk_empty_array_with_capacity(v___x_866_);
v___x_868_ = lean_array_push(v___x_867_, v___x_865_);
v___x_869_ = lean_expr_abstract(v_b_855_, v___x_868_);
lean_dec_ref(v___x_868_);
lean_dec_ref(v_b_855_);
if (v_isLet_861_ == 0)
{
uint8_t v___x_870_; lean_object* v___x_871_; 
v___x_870_ = 1;
v___x_871_ = l_Lean_Expr_letE___override(v___x_862_, v___x_863_, v___x_864_, v___x_869_, v___x_870_);
v_i_853_ = v___x_858_;
v_b_855_ = v___x_871_;
goto _start;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Expr_letE___override(v___x_862_, v___x_863_, v___x_864_, v___x_869_, v___x_856_);
v_i_853_ = v___x_858_;
v_b_855_ = v___x_873_;
goto _start;
}
}
else
{
return v_b_855_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_852_ = stack[0].m_obj;
size_t v_i_853_ = stack[1].m_num;
size_t v_stop_854_ = stack[2].m_num;
lean_object* v_b_855_ = stack[3].m_obj;
lean_object* v_res_875_;
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_852_, v_i_853_, v_stop_854_, v_b_855_);
stack->m_obj
 = v_res_875_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object* v_as_876_, lean_object* v_i_877_, lean_object* v_stop_878_, lean_object* v_b_879_){
_start:
{
size_t v_i_boxed_880_; size_t v_stop_boxed_881_; lean_object* v_res_882_; 
v_i_boxed_880_ = lean_unbox_usize(v_i_877_);
lean_dec(v_i_877_);
v_stop_boxed_881_ = lean_unbox_usize(v_stop_878_);
lean_dec(v_stop_878_);
v_res_882_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_876_, v_i_boxed_880_, v_stop_boxed_881_, v_b_879_);
lean_dec_ref(v_as_876_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object* v_decls_883_, lean_object* v_e_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_array_get_size(v_decls_883_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_nat_dec_lt(v___x_886_, v___x_885_);
if (v___x_887_ == 0)
{
return v_e_884_;
}
else
{
size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_usize_of_nat(v___x_885_);
v___x_889_ = ((size_t)0ULL);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_883_, v___x_888_, v___x_889_, v_e_884_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object* v_decls_891_, lean_object* v_e_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_891_, v_e_892_);
lean_dec_ref(v_decls_891_);
return v_res_893_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object* v_fvarId_894_, size_t v_sz_895_, size_t v_i_896_, lean_object* v_bs_897_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_lt(v_i_896_, v_sz_895_);
if (v___x_898_ == 0)
{
return v_bs_897_;
}
else
{
lean_object* v_v_899_; lean_object* v_decl_900_; lean_object* v___x_901_; lean_object* v_bs_x27_902_; lean_object* v___y_904_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_v_899_ = lean_array_uget(v_bs_897_, v_i_896_);
v_decl_900_ = lean_ctor_get(v_v_899_, 0);
v___x_901_ = lean_unsigned_to_nat(0u);
v_bs_x27_902_ = lean_array_uset(v_bs_897_, v_i_896_, v___x_901_);
v___x_909_ = l_Lean_LocalDecl_fvarId(v_decl_900_);
v___x_910_ = l_Lean_instBEqFVarId_beq(v___x_909_, v_fvarId_894_);
lean_dec(v___x_909_);
if (v___x_910_ == 0)
{
v___y_904_ = v_v_899_;
goto v___jp_903_;
}
else
{
lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_inc_ref(v_decl_900_);
v_isSharedCheck_917_ = !lean_is_exclusive(v_v_899_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_v_899_, 0);
lean_dec(v_unused_918_);
v___x_912_ = v_v_899_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_dec(v_v_899_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_decl_900_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_910_);
v___y_904_ = v___x_915_;
goto v___jp_903_;
}
}
}
v___jp_903_:
{
size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
v___x_905_ = ((size_t)1ULL);
v___x_906_ = lean_usize_add(v_i_896_, v___x_905_);
v___x_907_ = lean_array_uset(v_bs_x27_902_, v_i_896_, v___y_904_);
v_i_896_ = v___x_906_;
v_bs_897_ = v___x_907_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_894_ = stack[0].m_obj;
size_t v_sz_895_ = stack[1].m_num;
size_t v_i_896_ = stack[2].m_num;
lean_object* v_bs_897_ = stack[3].m_obj;
lean_object* v_res_919_;
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_894_, v_sz_895_, v_i_896_, v_bs_897_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object* v_fvarId_920_, lean_object* v_sz_921_, lean_object* v_i_922_, lean_object* v_bs_923_){
_start:
{
size_t v_sz_boxed_924_; size_t v_i_boxed_925_; lean_object* v_res_926_; 
v_sz_boxed_924_ = lean_unbox_usize(v_sz_921_);
lean_dec(v_sz_921_);
v_i_boxed_925_ = lean_unbox_usize(v_i_922_);
lean_dec(v_i_922_);
v_res_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_920_, v_sz_boxed_924_, v_i_boxed_925_, v_bs_923_);
lean_dec(v_fvarId_920_);
return v_res_926_;
}
}
lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object* v_fvarId_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_givenNames_931_; lean_object* v_decls_932_; lean_object* v_valueMap_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_946_; 
v___x_930_ = lean_st_ref_take(v_a_928_);
v_givenNames_931_ = lean_ctor_get(v___x_930_, 0);
v_decls_932_ = lean_ctor_get(v___x_930_, 1);
v_valueMap_933_ = lean_ctor_get(v___x_930_, 2);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_946_ == 0)
{
v___x_935_ = v___x_930_;
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_valueMap_933_);
lean_inc(v_decls_932_);
lean_inc(v_givenNames_931_);
lean_dec(v___x_930_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; size_t v_sz_938_; size_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_937_ = lean_box(0);
v_sz_938_ = lean_array_size(v_decls_932_);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_927_, v_sz_938_, v___x_939_, v_decls_932_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v___x_940_);
v___x_942_ = v___x_935_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_givenNames_931_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_valueMap_933_);
v___x_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_st_ref_put(v_a_928_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_937_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_ensureIsLet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_927_ = stack[0].m_obj;
lean_object* v_a_928_ = stack[1].m_obj;
lean_object* v_res_947_;
v_res_947_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_927_, v_a_928_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object* v_fvarId_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec(v_fvarId_948_);
return v_res_951_;
}
}
lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object* v_fvarId_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_952_, v_a_955_);
return v___x_961_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_ensureIsLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_952_ = stack[0].m_obj;
lean_object* v_a_953_ = stack[1].m_obj;
lean_object* v_a_954_ = stack[2].m_obj;
lean_object* v_a_955_ = stack[3].m_obj;
lean_object* v_a_956_ = stack[4].m_obj;
lean_object* v_a_957_ = stack[5].m_obj;
lean_object* v_a_958_ = stack[6].m_obj;
lean_object* v_a_959_ = stack[7].m_obj;
lean_object* v_res_962_;
v_res_962_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object* v_fvarId_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_fvarId_963_);
return v_res_972_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(size_t v_sz_973_, size_t v_i_974_, lean_object* v_bs_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_lt(v_i_974_, v_sz_973_);
if (v___x_976_ == 0)
{
return v_bs_975_;
}
else
{
lean_object* v_v_977_; lean_object* v_decl_978_; lean_object* v___x_979_; lean_object* v_bs_x27_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
v_v_977_ = lean_array_uget_borrowed(v_bs_975_, v_i_974_);
v_decl_978_ = lean_ctor_get(v_v_977_, 0);
lean_inc_ref(v_decl_978_);
v___x_979_ = lean_unsigned_to_nat(0u);
v_bs_x27_980_ = lean_array_uset(v_bs_975_, v_i_974_, v___x_979_);
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_974_, v___x_981_);
v___x_983_ = lean_array_uset(v_bs_x27_980_, v_i_974_, v_decl_978_);
v_i_974_ = v___x_982_;
v_bs_975_ = v___x_983_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_973_ = stack[0].m_num;
size_t v_i_974_ = stack[1].m_num;
lean_object* v_bs_975_ = stack[2].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_973_, v_i_974_, v_bs_975_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1___boxed(lean_object* v_sz_986_, lean_object* v_i_987_, lean_object* v_bs_988_){
_start:
{
size_t v_sz_boxed_989_; size_t v_i_boxed_990_; lean_object* v_res_991_; 
v_sz_boxed_989_ = lean_unbox_usize(v_sz_986_);
lean_dec(v_sz_986_);
v_i_boxed_990_ = lean_unbox_usize(v_i_987_);
lean_dec(v_i_987_);
v_res_991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_boxed_989_, v_i_boxed_990_, v_bs_988_);
return v_res_991_;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
lean_inc(v___y_995_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
v___x_1001_ = lean_apply_8(v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, lean_box(0));
return v___x_1001_;
}
}
LEAN_EXPORT void l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_992_ = stack[0].m_obj;
lean_object* v___y_993_ = stack[1].m_obj;
lean_object* v___y_994_ = stack[2].m_obj;
lean_object* v___y_995_ = stack[3].m_obj;
lean_object* v___y_996_ = stack[4].m_obj;
lean_object* v___y_997_ = stack[5].m_obj;
lean_object* v___y_998_ = stack[6].m_obj;
lean_object* v___y_999_ = stack[7].m_obj;
lean_object* v_res_1002_;
v_res_1002_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
stack->m_obj
 = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(v_x_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1012_;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(lean_object* v_decls_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___f_1023_; lean_object* v___x_1024_; 
lean_inc(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1023_, 0, v_x_1014_);
lean_closure_set(v___f_1023_, 1, v___y_1015_);
lean_closure_set(v___f_1023_, 2, v___y_1016_);
lean_closure_set(v___f_1023_, 3, v___y_1017_);
v___x_1024_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1013_, v___f_1023_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1024_) == 0)
{
return v___x_1024_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1013_ = stack[0].m_obj;
lean_object* v_x_1014_ = stack[1].m_obj;
lean_object* v___y_1015_ = stack[2].m_obj;
lean_object* v___y_1016_ = stack[3].m_obj;
lean_object* v___y_1017_ = stack[4].m_obj;
lean_object* v___y_1018_ = stack[5].m_obj;
lean_object* v___y_1019_ = stack[6].m_obj;
lean_object* v___y_1020_ = stack[7].m_obj;
lean_object* v___y_1021_ = stack[8].m_obj;
lean_object* v_res_1033_;
v_res_1033_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1013_, v_x_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
stack->m_obj
 = v_res_1033_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___boxed(lean_object* v_decls_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1034_, v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1044_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(lean_object* v___x_1045_, lean_object* v_as_1046_, size_t v_i_1047_, size_t v_stop_1048_, lean_object* v_b_1049_){
_start:
{
lean_object* v___y_1051_; uint8_t v___x_1055_; 
v___x_1055_ = lean_usize_dec_eq(v_i_1047_, v_stop_1048_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v_decl_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = lean_array_uget_borrowed(v_as_1046_, v_i_1047_);
v_decl_1057_ = lean_ctor_get(v___x_1056_, 0);
v___x_1058_ = l_Lean_LocalDecl_fvarId(v_decl_1057_);
v___x_1059_ = l_Lean_LocalContext_contains(v___x_1045_, v___x_1058_);
lean_dec(v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_inc(v___x_1056_);
v___x_1060_ = lean_array_push(v_b_1049_, v___x_1056_);
v___y_1051_ = v___x_1060_;
goto v___jp_1050_;
}
else
{
v___y_1051_ = v_b_1049_;
goto v___jp_1050_;
}
}
else
{
return v_b_1049_;
}
v___jp_1050_:
{
size_t v___x_1052_; size_t v___x_1053_; 
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1047_, v___x_1052_);
v_i_1047_ = v___x_1053_;
v_b_1049_ = v___y_1051_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1045_ = stack[0].m_obj;
lean_object* v_as_1046_ = stack[1].m_obj;
size_t v_i_1047_ = stack[2].m_num;
size_t v_stop_1048_ = stack[3].m_num;
lean_object* v_b_1049_ = stack[4].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_1045_, v_as_1046_, v_i_1047_, v_stop_1048_, v_b_1049_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(lean_object* v___x_1062_, lean_object* v_as_1063_, lean_object* v_i_1064_, lean_object* v_stop_1065_, lean_object* v_b_1066_){
_start:
{
size_t v_i_boxed_1067_; size_t v_stop_boxed_1068_; lean_object* v_res_1069_; 
v_i_boxed_1067_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_stop_boxed_1068_ = lean_unbox_usize(v_stop_1065_);
lean_dec(v_stop_1065_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_1062_, v_as_1063_, v_i_boxed_1067_, v_stop_boxed_1068_, v_b_1066_);
lean_dec_ref(v_as_1063_);
lean_dec_ref(v___x_1062_);
return v_res_1069_;
}
}
lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(lean_object* v_decls_1070_, lean_object* v_k_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___y_1081_; lean_object* v_lctx_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_lctx_1087_ = lean_ctor_get(v___y_1075_, 2);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_array_get_size(v_decls_1070_);
v___x_1090_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_1091_ = lean_nat_dec_lt(v___x_1088_, v___x_1089_);
if (v___x_1091_ == 0)
{
v___y_1081_ = v___x_1090_;
goto v___jp_1080_;
}
else
{
size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = ((size_t)0ULL);
v___x_1093_ = lean_usize_of_nat(v___x_1089_);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1087_, v_decls_1070_, v___x_1092_, v___x_1093_, v___x_1090_);
v___y_1081_ = v___x_1094_;
goto v___jp_1080_;
}
v___jp_1080_:
{
size_t v_sz_1082_; size_t v___x_1083_; lean_object* v_decls_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_sz_1082_ = lean_array_size(v___y_1081_);
v___x_1083_ = ((size_t)0ULL);
v_decls_1084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_1082_, v___x_1083_, v___y_1081_);
v___x_1085_ = lean_array_to_list(v_decls_1084_);
v___x_1086_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v___x_1085_, v_k_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v___x_1086_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1070_ = stack[0].m_obj;
lean_object* v_k_1071_ = stack[1].m_obj;
lean_object* v___y_1072_ = stack[2].m_obj;
lean_object* v___y_1073_ = stack[3].m_obj;
lean_object* v___y_1074_ = stack[4].m_obj;
lean_object* v___y_1075_ = stack[5].m_obj;
lean_object* v___y_1076_ = stack[6].m_obj;
lean_object* v___y_1077_ = stack[7].m_obj;
lean_object* v___y_1078_ = stack[8].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1070_, v_k_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object* v_decls_1096_, lean_object* v_k_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1096_, v_k_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v_decls_1096_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_fvarId_1107_, lean_object* v_as_1108_, lean_object* v_j_1109_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_array_get_size(v_as_1108_);
v___x_1111_ = lean_nat_dec_lt(v_j_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_j_1109_);
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v_decl_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1113_ = lean_array_fget_borrowed(v_as_1108_, v_j_1109_);
v_decl_1114_ = lean_ctor_get(v___x_1113_, 0);
v___x_1115_ = l_Lean_LocalDecl_fvarId(v_decl_1114_);
v___x_1116_ = l_Lean_instBEqFVarId_beq(v___x_1115_, v_fvarId_1107_);
lean_dec(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_j_1109_, v___x_1117_);
lean_dec(v_j_1109_);
v_j_1109_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_j_1109_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_fvarId_1121_, lean_object* v_as_1122_, lean_object* v_j_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1121_, v_as_1122_, v_j_1123_);
lean_dec_ref(v_as_1122_);
lean_dec(v_fvarId_1121_);
return v_res_1124_;
}
}
lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1125_, lean_object* v_k_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v_lctx_1136_; uint8_t v___x_1137_; 
v___x_1135_ = lean_st_ref_get(v_a_1129_);
v_lctx_1136_ = lean_ctor_get(v_a_1130_, 2);
v___x_1137_ = l_Lean_LocalContext_contains(v_lctx_1136_, v_fvarId_1125_);
if (v___x_1137_ == 0)
{
lean_object* v_decls_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_decls_1138_ = lean_ctor_get(v___x_1135_, 1);
lean_inc_ref(v_decls_1138_);
lean_dec(v___x_1135_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1125_, v_decls_1138_, v___x_1139_);
if (lean_obj_tag(v___x_1140_) == 1)
{
lean_object* v_val_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_val_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_val_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_add(v_val_1141_, v___x_1142_);
lean_dec(v_val_1141_);
v___x_1144_ = l_Array_toSubarray___redArg(v_decls_1138_, v___x_1139_, v___x_1143_);
v___x_1145_ = l_Subarray_copy___redArg(v___x_1144_);
v___x_1146_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_1145_, v_k_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec_ref(v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
lean_dec(v___x_1140_);
lean_dec_ref(v_decls_1138_);
lean_inc(v_a_1133_);
lean_inc_ref(v_a_1132_);
lean_inc(v_a_1131_);
lean_inc_ref(v_a_1130_);
lean_inc(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc_ref(v_a_1127_);
v___x_1147_ = lean_apply_8(v_k_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, lean_box(0));
return v___x_1147_;
}
}
else
{
lean_object* v___x_1148_; 
lean_dec(v___x_1135_);
lean_inc(v_a_1133_);
lean_inc_ref(v_a_1132_);
lean_inc(v_a_1131_);
lean_inc_ref(v_a_1130_);
lean_inc(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc_ref(v_a_1127_);
v___x_1148_ = lean_apply_8(v_k_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, lean_box(0));
return v___x_1148_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_withDeclInContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1125_ = stack[0].m_obj;
lean_object* v_k_1126_ = stack[1].m_obj;
lean_object* v_a_1127_ = stack[2].m_obj;
lean_object* v_a_1128_ = stack[3].m_obj;
lean_object* v_a_1129_ = stack[4].m_obj;
lean_object* v_a_1130_ = stack[5].m_obj;
lean_object* v_a_1131_ = stack[6].m_obj;
lean_object* v_a_1132_ = stack[7].m_obj;
lean_object* v_a_1133_ = stack[8].m_obj;
lean_object* v_res_1149_;
v_res_1149_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1125_, v_k_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1150_, lean_object* v_k_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1150_, v_k_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_fvarId_1150_);
return v_res_1160_;
}
}
lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1161_, lean_object* v_fvarId_1162_, lean_object* v_k_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1162_, v_k_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_withDeclInContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1162_ = stack[1].m_obj;
lean_object* v_k_1163_ = stack[2].m_obj;
lean_object* v_a_1164_ = stack[3].m_obj;
lean_object* v_a_1165_ = stack[4].m_obj;
lean_object* v_a_1166_ = stack[5].m_obj;
lean_object* v_a_1167_ = stack[6].m_obj;
lean_object* v_a_1168_ = stack[7].m_obj;
lean_object* v_a_1169_ = stack[8].m_obj;
lean_object* v_a_1170_ = stack[9].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l_Lean_Meta_ExtractLets_withDeclInContext(lean_box(0), v_fvarId_1162_, v_k_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1174_, lean_object* v_fvarId_1175_, lean_object* v_k_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1174_, v_fvarId_1175_, v_k_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_fvarId_1175_);
return v_res_1185_;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object* v_00_u03b1_1186_, lean_object* v_decls_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT void l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1187_ = stack[1].m_obj;
lean_object* v_x_1188_ = stack[2].m_obj;
lean_object* v___y_1189_ = stack[3].m_obj;
lean_object* v___y_1190_ = stack[4].m_obj;
lean_object* v___y_1191_ = stack[5].m_obj;
lean_object* v___y_1192_ = stack[6].m_obj;
lean_object* v___y_1193_ = stack[7].m_obj;
lean_object* v___y_1194_ = stack[8].m_obj;
lean_object* v___y_1195_ = stack[9].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_box(0), v_decls_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_decls_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_1199_, v_decls_1200_, v_x_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1210_;
}
}
lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object* v_00_u03b1_1211_, lean_object* v_decls_1212_, lean_object* v_k_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1212_, v_k_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1212_ = stack[1].m_obj;
lean_object* v_k_1213_ = stack[2].m_obj;
lean_object* v___y_1214_ = stack[3].m_obj;
lean_object* v___y_1215_ = stack[4].m_obj;
lean_object* v___y_1216_ = stack[5].m_obj;
lean_object* v___y_1217_ = stack[6].m_obj;
lean_object* v___y_1218_ = stack[7].m_obj;
lean_object* v___y_1219_ = stack[8].m_obj;
lean_object* v___y_1220_ = stack[9].m_obj;
lean_object* v_res_1223_;
v_res_1223_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_box(0), v_decls_1212_, v_k_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
stack->m_obj
 = v_res_1223_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_decls_1225_, lean_object* v_k_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_1224_, v_decls_1225_, v_k_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec_ref(v_decls_1225_);
return v_res_1235_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = l_Lean_Expr_hasMVar(v_e_1236_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_e_1236_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v_mctx_1242_; lean_object* v___x_1243_; lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1246_; lean_object* v_cache_1247_; lean_object* v_zetaDeltaFVarIds_1248_; lean_object* v_postponed_1249_; lean_object* v_diag_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1259_; 
v___x_1241_ = lean_st_ref_get(v___y_1237_);
v_mctx_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_mctx_1242_);
lean_dec(v___x_1241_);
v___x_1243_ = l_Lean_instantiateMVarsCore(v_mctx_1242_, v_e_1236_);
v_fst_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_fst_1244_);
v_snd_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_snd_1245_);
lean_dec_ref(v___x_1243_);
v___x_1246_ = lean_st_ref_take(v___y_1237_);
v_cache_1247_ = lean_ctor_get(v___x_1246_, 1);
v_zetaDeltaFVarIds_1248_ = lean_ctor_get(v___x_1246_, 2);
v_postponed_1249_ = lean_ctor_get(v___x_1246_, 3);
v_diag_1250_ = lean_ctor_get(v___x_1246_, 4);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1246_, 0);
lean_dec(v_unused_1260_);
v___x_1252_ = v___x_1246_;
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_diag_1250_);
lean_inc(v_postponed_1249_);
lean_inc(v_zetaDeltaFVarIds_1248_);
lean_inc(v_cache_1247_);
lean_dec(v___x_1246_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_snd_1245_);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_snd_1245_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_cache_1247_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_zetaDeltaFVarIds_1248_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_postponed_1249_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_diag_1250_);
v___x_1255_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_st_ref_put(v___y_1237_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_fst_1244_);
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1236_ = stack[0].m_obj;
lean_object* v___y_1237_ = stack[1].m_obj;
lean_object* v_res_1261_;
v_res_1261_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1236_, v___y_1237_);
stack->m_obj
 = v_res_1261_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1262_, v___y_1263_);
lean_dec(v___y_1263_);
return v_res_1265_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1266_, v___y_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1266_ = stack[0].m_obj;
lean_object* v___y_1267_ = stack[1].m_obj;
lean_object* v___y_1268_ = stack[2].m_obj;
lean_object* v___y_1269_ = stack[3].m_obj;
lean_object* v___y_1270_ = stack[4].m_obj;
lean_object* v___y_1271_ = stack[5].m_obj;
lean_object* v___y_1272_ = stack[6].m_obj;
lean_object* v___y_1273_ = stack[7].m_obj;
lean_object* v_res_1276_;
v_res_1276_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
stack->m_obj
 = v_res_1276_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1286_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1287_, size_t v_i_1288_, size_t v_stop_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_a_1300_; uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_eq(v_i_1288_, v_stop_1289_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_array_uget_borrowed(v_as_1287_, v_i_1288_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_box(0);
v_a_1300_ = v___x_1308_;
goto v___jp_1299_;
}
else
{
lean_object* v_val_1309_; uint8_t v___y_1311_; uint8_t v___x_1338_; 
v_val_1309_ = lean_ctor_get(v___x_1307_, 0);
v___x_1338_ = l_Lean_LocalDecl_isLet(v_val_1309_, v___x_1306_);
if (v___x_1338_ == 0)
{
v___y_1311_ = v___x_1338_;
goto v___jp_1310_;
}
else
{
uint8_t v___x_1339_; 
v___x_1339_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1309_);
if (v___x_1339_ == 0)
{
v___y_1311_ = v___x_1338_;
goto v___jp_1310_;
}
else
{
goto v___jp_1304_;
}
}
v___jp_1310_:
{
if (v___y_1311_ == 0)
{
goto v___jp_1304_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = l_Lean_LocalDecl_value(v_val_1309_, v___x_1306_);
v___x_1313_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1312_, v___y_1295_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; lean_object* v_givenNames_1316_; lean_object* v_decls_1317_; lean_object* v_valueMap_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1329_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___x_1315_ = lean_st_ref_take(v___y_1293_);
v_givenNames_1316_ = lean_ctor_get(v___x_1315_, 0);
v_decls_1317_ = lean_ctor_get(v___x_1315_, 1);
v_valueMap_1318_ = lean_ctor_get(v___x_1315_, 2);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1320_ = v___x_1315_;
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_valueMap_1318_);
lean_inc(v_decls_1317_);
lean_inc(v_givenNames_1316_);
lean_dec(v___x_1315_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = l_Lean_LocalDecl_fvarId(v_val_1309_);
v___x_1324_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1318_, v_a_1314_, v___x_1323_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 2, v___x_1324_);
v___x_1326_ = v___x_1320_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_givenNames_1316_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_decls_1317_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_st_ref_put(v___y_1293_, v___x_1326_);
v_a_1300_ = v___x_1322_;
goto v___jp_1299_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1313_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1313_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_b_1290_);
return v___x_1340_;
}
v___jp_1299_:
{
size_t v___x_1301_; size_t v___x_1302_; 
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_i_1288_, v___x_1301_);
v_i_1288_ = v___x_1302_;
v_b_1290_ = v_a_1300_;
goto _start;
}
v___jp_1304_:
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_box(0);
v_a_1300_ = v___x_1305_;
goto v___jp_1299_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1287_ = stack[0].m_obj;
size_t v_i_1288_ = stack[1].m_num;
size_t v_stop_1289_ = stack[2].m_num;
lean_object* v_b_1290_ = stack[3].m_obj;
lean_object* v___y_1291_ = stack[4].m_obj;
lean_object* v___y_1292_ = stack[5].m_obj;
lean_object* v___y_1293_ = stack[6].m_obj;
lean_object* v___y_1294_ = stack[7].m_obj;
lean_object* v___y_1295_ = stack[8].m_obj;
lean_object* v___y_1296_ = stack[9].m_obj;
lean_object* v___y_1297_ = stack[10].m_obj;
lean_object* v_res_1341_;
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1287_, v_i_1288_, v_stop_1289_, v_b_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1342_, lean_object* v_i_1343_, lean_object* v_stop_1344_, lean_object* v_b_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
size_t v_i_boxed_1354_; size_t v_stop_boxed_1355_; lean_object* v_res_1356_; 
v_i_boxed_1354_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_stop_boxed_1355_ = lean_unbox_usize(v_stop_1344_);
lean_dec(v_stop_1344_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1342_, v_i_boxed_1354_, v_stop_boxed_1355_, v_b_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec_ref(v_as_1342_);
return v_res_1356_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1357_, size_t v_i_1358_, size_t v_stop_1359_, lean_object* v_b_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_a_1370_; uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_eq(v_i_1358_, v_stop_1359_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_array_uget_borrowed(v_as_1357_, v_i_1358_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_box(0);
v_a_1370_ = v___x_1378_;
goto v___jp_1369_;
}
else
{
lean_object* v_val_1379_; uint8_t v___y_1381_; uint8_t v___x_1408_; 
v_val_1379_ = lean_ctor_get(v___x_1377_, 0);
v___x_1408_ = l_Lean_LocalDecl_isLet(v_val_1379_, v___x_1376_);
if (v___x_1408_ == 0)
{
v___y_1381_ = v___x_1408_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1379_);
if (v___x_1409_ == 0)
{
v___y_1381_ = v___x_1408_;
goto v___jp_1380_;
}
else
{
goto v___jp_1374_;
}
}
v___jp_1380_:
{
if (v___y_1381_ == 0)
{
goto v___jp_1374_;
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = l_Lean_LocalDecl_value(v_val_1379_, v___x_1376_);
v___x_1383_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1382_, v___y_1365_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v_givenNames_1386_; lean_object* v_decls_1387_; lean_object* v_valueMap_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1399_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = lean_st_ref_take(v___y_1363_);
v_givenNames_1386_ = lean_ctor_get(v___x_1385_, 0);
v_decls_1387_ = lean_ctor_get(v___x_1385_, 1);
v_valueMap_1388_ = lean_ctor_get(v___x_1385_, 2);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1390_ = v___x_1385_;
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_valueMap_1388_);
lean_inc(v_decls_1387_);
lean_inc(v_givenNames_1386_);
lean_dec(v___x_1385_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1392_ = lean_box(0);
v___x_1393_ = l_Lean_LocalDecl_fvarId(v_val_1379_);
v___x_1394_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1388_, v_a_1384_, v___x_1393_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 2, v___x_1394_);
v___x_1396_ = v___x_1390_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_givenNames_1386_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_decls_1387_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_st_ref_put(v___y_1363_, v___x_1396_);
v_a_1370_ = v___x_1392_;
goto v___jp_1369_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1400_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1383_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1383_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_b_1360_);
return v___x_1410_;
}
v___jp_1369_:
{
size_t v___x_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = ((size_t)1ULL);
v___x_1372_ = lean_usize_add(v_i_1358_, v___x_1371_);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1357_, v___x_1372_, v_stop_1359_, v_a_1370_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1373_;
}
v___jp_1374_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_box(0);
v_a_1370_ = v___x_1375_;
goto v___jp_1369_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1357_ = stack[0].m_obj;
size_t v_i_1358_ = stack[1].m_num;
size_t v_stop_1359_ = stack[2].m_num;
lean_object* v_b_1360_ = stack[3].m_obj;
lean_object* v___y_1361_ = stack[4].m_obj;
lean_object* v___y_1362_ = stack[5].m_obj;
lean_object* v___y_1363_ = stack[6].m_obj;
lean_object* v___y_1364_ = stack[7].m_obj;
lean_object* v___y_1365_ = stack[8].m_obj;
lean_object* v___y_1366_ = stack[9].m_obj;
lean_object* v___y_1367_ = stack[10].m_obj;
lean_object* v_res_1411_;
v_res_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1357_, v_i_1358_, v_stop_1359_, v_b_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
stack->m_obj
 = v_res_1411_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1412_, lean_object* v_i_1413_, lean_object* v_stop_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
size_t v_i_boxed_1424_; size_t v_stop_boxed_1425_; lean_object* v_res_1426_; 
v_i_boxed_1424_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_stop_boxed_1425_ = lean_unbox_usize(v_stop_1414_);
lean_dec(v_stop_1414_);
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1412_, v_i_boxed_1424_, v_stop_boxed_1425_, v_b_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v_as_1412_);
return v_res_1426_;
}
}
lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
lean_object* v_cs_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1450_; 
v_cs_1436_ = lean_ctor_get(v_x_1427_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_x_1427_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1438_ = v_x_1427_;
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_cs_1436_);
lean_dec(v_x_1427_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = lean_array_get_size(v_cs_1436_);
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_nat_dec_lt(v___x_1440_, v___x_1441_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref(v_cs_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1442_);
v___x_1445_ = v___x_1438_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1442_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
size_t v___x_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
lean_del_object(v___x_1438_);
v___x_1447_ = ((size_t)0ULL);
v___x_1448_ = lean_usize_of_nat(v___x_1441_);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1436_, v___x_1447_, v___x_1448_, v___x_1442_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec_ref(v_cs_1436_);
return v___x_1449_;
}
}
}
else
{
lean_object* v_vs_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1465_; 
v_vs_1451_ = lean_ctor_get(v_x_1427_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1427_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1453_ = v_x_1427_;
v_isShared_1454_ = v_isSharedCheck_1465_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_vs_1451_);
lean_dec(v_x_1427_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1465_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_array_get_size(v_vs_1451_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_nat_dec_lt(v___x_1455_, v___x_1456_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_vs_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set_tag(v___x_1453_, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1457_);
v___x_1460_ = v___x_1453_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1457_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
lean_del_object(v___x_1453_);
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = lean_usize_of_nat(v___x_1456_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1451_, v___x_1462_, v___x_1463_, v___x_1457_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec_ref(v_vs_1451_);
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1427_ = stack[0].m_obj;
lean_object* v___y_1428_ = stack[1].m_obj;
lean_object* v___y_1429_ = stack[2].m_obj;
lean_object* v___y_1430_ = stack[3].m_obj;
lean_object* v___y_1431_ = stack[4].m_obj;
lean_object* v___y_1432_ = stack[5].m_obj;
lean_object* v___y_1433_ = stack[6].m_obj;
lean_object* v___y_1434_ = stack[7].m_obj;
lean_object* v_res_1466_;
v_res_1466_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
stack->m_obj
 = v_res_1466_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1467_, size_t v_i_1468_, size_t v_stop_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_usize_dec_eq(v_i_1468_, v_stop_1469_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_array_uget_borrowed(v_as_1467_, v_i_1468_);
lean_inc(v___x_1480_);
v___x_1481_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1480_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; size_t v___x_1483_; size_t v___x_1484_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = ((size_t)1ULL);
v___x_1484_ = lean_usize_add(v_i_1468_, v___x_1483_);
v_i_1468_ = v___x_1484_;
v_b_1470_ = v_a_1482_;
goto _start;
}
else
{
return v___x_1481_;
}
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1470_);
return v___x_1486_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1467_ = stack[0].m_obj;
size_t v_i_1468_ = stack[1].m_num;
size_t v_stop_1469_ = stack[2].m_num;
lean_object* v_b_1470_ = stack[3].m_obj;
lean_object* v___y_1471_ = stack[4].m_obj;
lean_object* v___y_1472_ = stack[5].m_obj;
lean_object* v___y_1473_ = stack[6].m_obj;
lean_object* v___y_1474_ = stack[7].m_obj;
lean_object* v___y_1475_ = stack[8].m_obj;
lean_object* v___y_1476_ = stack[9].m_obj;
lean_object* v___y_1477_ = stack[10].m_obj;
lean_object* v_res_1487_;
v_res_1487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1467_, v_i_1468_, v_stop_1469_, v_b_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
stack->m_obj
 = v_res_1487_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1488_, lean_object* v_i_1489_, lean_object* v_stop_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
size_t v_i_boxed_1500_; size_t v_stop_boxed_1501_; lean_object* v_res_1502_; 
v_i_boxed_1500_ = lean_unbox_usize(v_i_1489_);
lean_dec(v_i_1489_);
v_stop_boxed_1501_ = lean_unbox_usize(v_stop_1490_);
lean_dec(v_stop_1490_);
v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1488_, v_i_boxed_1500_, v_stop_boxed_1501_, v_b_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec_ref(v_as_1488_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1512_;
}
}
lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_root_1522_; lean_object* v_tail_1523_; lean_object* v___x_1524_; 
v_root_1522_ = lean_ctor_get(v_t_1513_, 0);
lean_inc_ref(v_root_1522_);
v_tail_1523_ = lean_ctor_get(v_t_1513_, 1);
lean_inc_ref(v_tail_1523_);
lean_dec_ref(v_t_1513_);
v___x_1524_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1522_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1538_; 
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v___x_1524_, 0);
lean_dec(v_unused_1539_);
v___x_1526_ = v___x_1524_;
v_isShared_1527_ = v_isSharedCheck_1538_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v___x_1524_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1538_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_array_get_size(v_tail_1523_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_nat_dec_lt(v___x_1528_, v___x_1529_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1533_; 
lean_dec_ref(v_tail_1523_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1530_);
v___x_1533_ = v___x_1526_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1530_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
else
{
size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
lean_del_object(v___x_1526_);
v___x_1535_ = ((size_t)0ULL);
v___x_1536_ = lean_usize_of_nat(v___x_1529_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1523_, v___x_1535_, v___x_1536_, v___x_1530_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec_ref(v_tail_1523_);
return v___x_1537_;
}
}
}
else
{
lean_dec_ref(v_tail_1523_);
return v___x_1524_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1513_ = stack[0].m_obj;
lean_object* v___y_1514_ = stack[1].m_obj;
lean_object* v___y_1515_ = stack[2].m_obj;
lean_object* v___y_1516_ = stack[3].m_obj;
lean_object* v___y_1517_ = stack[4].m_obj;
lean_object* v___y_1518_ = stack[5].m_obj;
lean_object* v___y_1519_ = stack[6].m_obj;
lean_object* v___y_1520_ = stack[7].m_obj;
lean_object* v_res_1540_;
v_res_1540_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1550_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1551_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1552_, size_t v_x_1553_, size_t v_x_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 0)
{
lean_object* v_cs_1563_; lean_object* v___x_1564_; size_t v___x_1565_; lean_object* v_j_1566_; lean_object* v___x_1567_; size_t v___x_1568_; size_t v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v_cs_1563_ = lean_ctor_get(v_x_1552_, 0);
lean_inc_ref(v_cs_1563_);
lean_dec_ref_known(v_x_1552_, 1);
v___x_1564_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1565_ = lean_usize_shift_right(v_x_1553_, v_x_1554_);
v_j_1566_ = lean_usize_to_nat(v___x_1565_);
v___x_1567_ = lean_array_get_borrowed(v___x_1564_, v_cs_1563_, v_j_1566_);
v___x_1568_ = ((size_t)1ULL);
v___x_1569_ = lean_usize_shift_left(v___x_1568_, v_x_1554_);
v___x_1570_ = lean_usize_sub(v___x_1569_, v___x_1568_);
v___x_1571_ = lean_usize_land(v_x_1553_, v___x_1570_);
v___x_1572_ = ((size_t)5ULL);
v___x_1573_ = lean_usize_sub(v_x_1554_, v___x_1572_);
lean_inc(v___x_1567_);
v___x_1574_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1567_, v___x_1571_, v___x_1573_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1589_; 
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v___x_1574_, 0);
lean_dec(v_unused_1590_);
v___x_1576_ = v___x_1574_;
v_isShared_1577_ = v_isSharedCheck_1589_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v___x_1574_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1589_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_j_1566_, v___x_1578_);
lean_dec(v_j_1566_);
v___x_1580_ = lean_array_get_size(v_cs_1563_);
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_nat_dec_lt(v___x_1579_, v___x_1580_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1584_; 
lean_dec(v___x_1579_);
lean_dec_ref(v_cs_1563_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1581_);
v___x_1584_ = v___x_1576_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1581_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
else
{
size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
lean_del_object(v___x_1576_);
v___x_1586_ = lean_usize_of_nat(v___x_1579_);
lean_dec(v___x_1579_);
v___x_1587_ = lean_usize_of_nat(v___x_1580_);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1563_, v___x_1586_, v___x_1587_, v___x_1581_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec_ref(v_cs_1563_);
return v___x_1588_;
}
}
}
else
{
lean_dec(v_j_1566_);
lean_dec_ref(v_cs_1563_);
return v___x_1574_;
}
}
else
{
lean_object* v_vs_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1605_; 
v_vs_1591_ = lean_ctor_get(v_x_1552_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_x_1552_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1593_ = v_x_1552_;
v_isShared_1594_ = v_isSharedCheck_1605_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_vs_1591_);
lean_dec(v_x_1552_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1605_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1595_ = lean_usize_to_nat(v_x_1553_);
v___x_1596_ = lean_array_get_size(v_vs_1591_);
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_nat_dec_lt(v___x_1595_, v___x_1596_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1600_; 
lean_dec(v___x_1595_);
lean_dec_ref(v_vs_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1597_);
v___x_1600_ = v___x_1593_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1597_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
lean_del_object(v___x_1593_);
v___x_1602_ = lean_usize_of_nat(v___x_1595_);
lean_dec(v___x_1595_);
v___x_1603_ = lean_usize_of_nat(v___x_1596_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1591_, v___x_1602_, v___x_1603_, v___x_1597_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec_ref(v_vs_1591_);
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1552_ = stack[0].m_obj;
size_t v_x_1553_ = stack[1].m_num;
size_t v_x_1554_ = stack[2].m_num;
lean_object* v___y_1555_ = stack[3].m_obj;
lean_object* v___y_1556_ = stack[4].m_obj;
lean_object* v___y_1557_ = stack[5].m_obj;
lean_object* v___y_1558_ = stack[6].m_obj;
lean_object* v___y_1559_ = stack[7].m_obj;
lean_object* v___y_1560_ = stack[8].m_obj;
lean_object* v___y_1561_ = stack[9].m_obj;
lean_object* v_res_1606_;
v_res_1606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1552_, v_x_1553_, v_x_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
stack->m_obj
 = v_res_1606_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
size_t v_x_9437__boxed_1618_; size_t v_x_9438__boxed_1619_; lean_object* v_res_1620_; 
v_x_9437__boxed_1618_ = lean_unbox_usize(v_x_1608_);
lean_dec(v_x_1608_);
v_x_9438__boxed_1619_ = lean_unbox_usize(v_x_1609_);
lean_dec(v_x_1609_);
v_res_1620_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1607_, v_x_9437__boxed_1618_, v_x_9438__boxed_1619_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1620_;
}
}
lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1621_, lean_object* v_start_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = lean_nat_dec_eq(v_start_1622_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v_root_1633_; lean_object* v_tail_1634_; size_t v_shift_1635_; lean_object* v_tailOff_1636_; uint8_t v___x_1637_; 
v_root_1633_ = lean_ctor_get(v_t_1621_, 0);
lean_inc_ref(v_root_1633_);
v_tail_1634_ = lean_ctor_get(v_t_1621_, 1);
lean_inc_ref(v_tail_1634_);
v_shift_1635_ = lean_ctor_get_usize(v_t_1621_, 4);
v_tailOff_1636_ = lean_ctor_get(v_t_1621_, 3);
lean_inc(v_tailOff_1636_);
lean_dec_ref(v_t_1621_);
v___x_1637_ = lean_nat_dec_le(v_tailOff_1636_, v_start_1622_);
if (v___x_1637_ == 0)
{
size_t v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_tailOff_1636_);
v___x_1638_ = lean_usize_of_nat(v_start_1622_);
v___x_1639_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1633_, v___x_1638_, v_shift_1635_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1652_; 
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; 
v_unused_1653_ = lean_ctor_get(v___x_1639_, 0);
lean_dec(v_unused_1653_);
v___x_1641_ = v___x_1639_;
v_isShared_1642_ = v_isSharedCheck_1652_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v___x_1639_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1652_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_array_get_size(v_tail_1634_);
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_nat_dec_lt(v___x_1631_, v___x_1643_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v_tail_1634_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1644_);
v___x_1647_ = v___x_1641_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1644_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
else
{
size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
lean_del_object(v___x_1641_);
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = lean_usize_of_nat(v___x_1643_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1634_, v___x_1649_, v___x_1650_, v___x_1644_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v_tail_1634_);
return v___x_1651_;
}
}
}
else
{
lean_dec_ref(v_tail_1634_);
return v___x_1639_;
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
lean_dec_ref(v_root_1633_);
v___x_1654_ = lean_nat_sub(v_start_1622_, v_tailOff_1636_);
lean_dec(v_tailOff_1636_);
v___x_1655_ = lean_array_get_size(v_tail_1634_);
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_nat_dec_lt(v___x_1654_, v___x_1655_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec(v___x_1654_);
lean_dec_ref(v_tail_1634_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
return v___x_1658_;
}
else
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_usize_of_nat(v___x_1654_);
lean_dec(v___x_1654_);
v___x_1660_ = lean_usize_of_nat(v___x_1655_);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1634_, v___x_1659_, v___x_1660_, v___x_1656_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v_tail_1634_);
return v___x_1661_;
}
}
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1621_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1662_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1621_ = stack[0].m_obj;
lean_object* v_start_1622_ = stack[1].m_obj;
lean_object* v___y_1623_ = stack[2].m_obj;
lean_object* v___y_1624_ = stack[3].m_obj;
lean_object* v___y_1625_ = stack[4].m_obj;
lean_object* v___y_1626_ = stack[5].m_obj;
lean_object* v___y_1627_ = stack[6].m_obj;
lean_object* v___y_1628_ = stack[7].m_obj;
lean_object* v___y_1629_ = stack[8].m_obj;
lean_object* v_res_1663_;
v_res_1663_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1621_, v_start_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
stack->m_obj
 = v_res_1663_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1664_, lean_object* v_start_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1664_, v_start_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v_start_1665_);
return v_res_1674_;
}
}
lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1675_, lean_object* v_start_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_decls_1685_; lean_object* v___x_1686_; 
v_decls_1685_ = lean_ctor_get(v_lctx_1675_, 1);
lean_inc_ref(v_decls_1685_);
lean_dec_ref(v_lctx_1675_);
v___x_1686_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1685_, v_start_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1686_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1675_ = stack[0].m_obj;
lean_object* v_start_1676_ = stack[1].m_obj;
lean_object* v___y_1677_ = stack[2].m_obj;
lean_object* v___y_1678_ = stack[3].m_obj;
lean_object* v___y_1679_ = stack[4].m_obj;
lean_object* v___y_1680_ = stack[5].m_obj;
lean_object* v___y_1681_ = stack[6].m_obj;
lean_object* v___y_1682_ = stack[7].m_obj;
lean_object* v___y_1683_ = stack[8].m_obj;
lean_object* v_res_1687_;
v_res_1687_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1675_, v_start_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
stack->m_obj
 = v_res_1687_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1688_, lean_object* v_start_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1688_, v_start_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v_start_1689_);
return v_res_1698_;
}
}
lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_lctx_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_lctx_1707_ = lean_ctor_get(v_a_1702_, 2);
v___x_1708_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1707_);
v___x_1709_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1707_, v___x_1708_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
return v___x_1709_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_initializeValueMap_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1699_ = stack[0].m_obj;
lean_object* v_a_1700_ = stack[1].m_obj;
lean_object* v_a_1701_ = stack[2].m_obj;
lean_object* v_a_1702_ = stack[3].m_obj;
lean_object* v_a_1703_ = stack[4].m_obj;
lean_object* v_a_1704_ = stack[5].m_obj;
lean_object* v_a_1705_ = stack[6].m_obj;
lean_object* v_res_1710_;
v_res_1710_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
stack->m_obj
 = v_res_1710_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1719_;
}
}
uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1721_){
_start:
{
lean_object* v___f_1722_; lean_object* v___x_1723_; 
v___f_1722_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1723_ = lean_find_expr(v___f_1722_, v_e_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
uint8_t v___x_1724_; 
v___x_1724_ = 0;
return v___x_1724_;
}
else
{
uint8_t v___x_1725_; 
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = 1;
return v___x_1725_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_containsLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1721_ = stack[0].m_obj;
uint8_t v_res_1726_;
v_res_1726_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1721_);
stack->m_num = v_res_1726_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1727_){
_start:
{
uint8_t v_res_1728_; lean_object* v_r_1729_; 
v_res_1728_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1727_);
lean_dec_ref(v_e_1727_);
v_r_1729_ = lean_box(v_res_1728_);
return v_r_1729_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
v___x_1740_ = lean_apply_9(v_k_1730_, v_b_1734_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, lean_box(0));
return v___x_1740_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1730_ = stack[0].m_obj;
lean_object* v___y_1731_ = stack[1].m_obj;
lean_object* v___y_1732_ = stack[2].m_obj;
lean_object* v___y_1733_ = stack[3].m_obj;
lean_object* v_b_1734_ = stack[4].m_obj;
lean_object* v___y_1735_ = stack[5].m_obj;
lean_object* v___y_1736_ = stack[6].m_obj;
lean_object* v___y_1737_ = stack[7].m_obj;
lean_object* v___y_1738_ = stack[8].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v_b_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v_b_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1752_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1753_, uint8_t v_bi_1754_, lean_object* v_type_1755_, lean_object* v_k_1756_, uint8_t v_kind_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___f_1766_; lean_object* v___x_1767_; 
lean_inc(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
v___f_1766_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1766_, 0, v_k_1756_);
lean_closure_set(v___f_1766_, 1, v___y_1758_);
lean_closure_set(v___f_1766_, 2, v___y_1759_);
lean_closure_set(v___f_1766_, 3, v___y_1760_);
v___x_1767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1753_, v_bi_1754_, v_type_1755_, v___f_1766_, v_kind_1757_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
if (lean_obj_tag(v___x_1767_) == 0)
{
return v___x_1767_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1753_ = stack[0].m_obj;
uint8_t v_bi_1754_ = stack[1].m_num;
lean_object* v_type_1755_ = stack[2].m_obj;
lean_object* v_k_1756_ = stack[3].m_obj;
uint8_t v_kind_1757_ = stack[4].m_num;
lean_object* v___y_1758_ = stack[5].m_obj;
lean_object* v___y_1759_ = stack[6].m_obj;
lean_object* v___y_1760_ = stack[7].m_obj;
lean_object* v___y_1761_ = stack[8].m_obj;
lean_object* v___y_1762_ = stack[9].m_obj;
lean_object* v___y_1763_ = stack[10].m_obj;
lean_object* v___y_1764_ = stack[11].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1753_, v_bi_1754_, v_type_1755_, v_k_1756_, v_kind_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1777_, lean_object* v_bi_1778_, lean_object* v_type_1779_, lean_object* v_k_1780_, lean_object* v_kind_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
uint8_t v_bi_boxed_1790_; uint8_t v_kind_boxed_1791_; lean_object* v_res_1792_; 
v_bi_boxed_1790_ = lean_unbox(v_bi_1778_);
v_kind_boxed_1791_ = lean_unbox(v_kind_1781_);
v_res_1792_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1777_, v_bi_boxed_1790_, v_type_1779_, v_k_1780_, v_kind_boxed_1791_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v_res_1792_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1793_, lean_object* v_name_1794_, uint8_t v_bi_1795_, lean_object* v_type_1796_, lean_object* v_k_1797_, uint8_t v_kind_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1794_, v_bi_1795_, v_type_1796_, v_k_1797_, v_kind_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1794_ = stack[1].m_obj;
uint8_t v_bi_1795_ = stack[2].m_num;
lean_object* v_type_1796_ = stack[3].m_obj;
lean_object* v_k_1797_ = stack[4].m_obj;
uint8_t v_kind_1798_ = stack[5].m_num;
lean_object* v___y_1799_ = stack[6].m_obj;
lean_object* v___y_1800_ = stack[7].m_obj;
lean_object* v___y_1801_ = stack[8].m_obj;
lean_object* v___y_1802_ = stack[9].m_obj;
lean_object* v___y_1803_ = stack[10].m_obj;
lean_object* v___y_1804_ = stack[11].m_obj;
lean_object* v___y_1805_ = stack[12].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_box(0), v_name_1794_, v_bi_1795_, v_type_1796_, v_k_1797_, v_kind_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_name_1810_, lean_object* v_bi_1811_, lean_object* v_type_1812_, lean_object* v_k_1813_, lean_object* v_kind_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v_bi_boxed_1823_; uint8_t v_kind_boxed_1824_; lean_object* v_res_1825_; 
v_bi_boxed_1823_ = lean_unbox(v_bi_1811_);
v_kind_boxed_1824_ = lean_unbox(v_kind_1814_);
v_res_1825_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1809_, v_name_1810_, v_bi_boxed_1823_, v_type_1812_, v_k_1813_, v_kind_boxed_1824_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v_res_1825_;
}
}
lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1826_, lean_object* v_e_1827_, lean_object* v___f_1828_, lean_object* v_____r_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
if (v_types_1826_ == 0)
{
lean_object* v___x_1838_; 
lean_inc_ref(v_e_1827_);
v___x_1838_ = l_Lean_Meta_isType(v_e_1827_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1849_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1849_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1849_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_unbox(v_a_1839_);
lean_dec(v_a_1839_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_del_object(v___x_1841_);
lean_dec_ref(v_e_1827_);
v___x_1844_ = lean_box(0);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1845_ = lean_apply_9(v___f_1828_, v___x_1844_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, lean_box(0));
return v___x_1845_;
}
else
{
lean_object* v___x_1847_; 
lean_dec_ref(v___f_1828_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_e_1827_);
v___x_1847_ = v___x_1841_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_e_1827_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v___f_1828_);
lean_dec_ref(v_e_1827_);
v_a_1850_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1838_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1838_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_e_1827_);
v___x_1858_ = lean_box(0);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1859_ = lean_apply_9(v___f_1828_, v___x_1858_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, lean_box(0));
return v___x_1859_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractCore___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_types_1826_ = stack[0].m_num;
lean_object* v_e_1827_ = stack[1].m_obj;
lean_object* v___f_1828_ = stack[2].m_obj;
lean_object* v_____r_1829_ = stack[3].m_obj;
lean_object* v___y_1830_ = stack[4].m_obj;
lean_object* v___y_1831_ = stack[5].m_obj;
lean_object* v___y_1832_ = stack[6].m_obj;
lean_object* v___y_1833_ = stack[7].m_obj;
lean_object* v___y_1834_ = stack[8].m_obj;
lean_object* v___y_1835_ = stack[9].m_obj;
lean_object* v___y_1836_ = stack[10].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_1826_, v_e_1827_, v___f_1828_, v_____r_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1861_, lean_object* v_e_1862_, lean_object* v___f_1863_, lean_object* v_____r_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v_types_boxed_1873_; lean_object* v_res_1874_; 
v_types_boxed_1873_ = lean_unbox(v_types_1861_);
v_res_1874_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1873_, v_e_1862_, v___f_1863_, v_____r_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1874_;
}
}
uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1875_, uint8_t v___y_1876_){
_start:
{
if (v___y_1876_ == 0)
{
if (v___y_1875_ == 0)
{
uint8_t v___x_1877_; 
v___x_1877_ = 1;
return v___x_1877_;
}
else
{
return v___y_1876_;
}
}
else
{
return v___y_1875_;
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1875_ = stack[0].m_num;
uint8_t v___y_1876_ = stack[1].m_num;
uint8_t v_res_1878_;
v_res_1878_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_1875_, v___y_1876_);
stack->m_num = v_res_1878_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v___y_41257__boxed_1881_; uint8_t v___y_41258__boxed_1882_; uint8_t v_res_1883_; lean_object* v_r_1884_; 
v___y_41257__boxed_1881_ = lean_unbox(v___y_1879_);
v___y_41258__boxed_1882_ = lean_unbox(v___y_1880_);
v_res_1883_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_41257__boxed_1881_, v___y_41258__boxed_1882_);
v_r_1884_ = lean_box(v_res_1883_);
return v_r_1884_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_instMonadEIO___redArg();
return v___x_1885_;
}
}
lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_toApplicative_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1976_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1904_ = l_StateRefT_x27_instMonad___redArg(v___x_1903_);
v_toApplicative_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v___x_1904_, 1);
lean_dec(v_unused_1977_);
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1976_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_toApplicative_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1976_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_toFunctor_1909_; lean_object* v_toSeq_1910_; lean_object* v_toSeqLeft_1911_; lean_object* v_toSeqRight_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1974_; 
v_toFunctor_1909_ = lean_ctor_get(v_toApplicative_1905_, 0);
v_toSeq_1910_ = lean_ctor_get(v_toApplicative_1905_, 2);
v_toSeqLeft_1911_ = lean_ctor_get(v_toApplicative_1905_, 3);
v_toSeqRight_1912_ = lean_ctor_get(v_toApplicative_1905_, 4);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_toApplicative_1905_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_toApplicative_1905_, 1);
lean_dec(v_unused_1975_);
v___x_1914_ = v_toApplicative_1905_;
v_isShared_1915_ = v_isSharedCheck_1974_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_toSeqRight_1912_);
lean_inc(v_toSeqLeft_1911_);
lean_inc(v_toSeq_1910_);
lean_inc(v_toFunctor_1909_);
lean_dec(v_toApplicative_1905_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1974_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___f_1916_; lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___f_1921_; lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___x_1925_; 
v___f_1916_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1917_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1909_);
v___f_1918_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1918_, 0, v_toFunctor_1909_);
v___f_1919_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1919_, 0, v_toFunctor_1909_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___f_1918_);
lean_ctor_set(v___x_1920_, 1, v___f_1919_);
v___f_1921_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1921_, 0, v_toSeqRight_1912_);
v___f_1922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1922_, 0, v_toSeqLeft_1911_);
v___f_1923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1923_, 0, v_toSeq_1910_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 4, v___f_1921_);
lean_ctor_set(v___x_1914_, 3, v___f_1922_);
lean_ctor_set(v___x_1914_, 2, v___f_1923_);
lean_ctor_set(v___x_1914_, 1, v___f_1916_);
lean_ctor_set(v___x_1914_, 0, v___x_1920_);
v___x_1925_ = v___x_1914_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___f_1916_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v___f_1923_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v___f_1922_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v___f_1921_);
v___x_1925_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1927_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v___f_1917_);
lean_ctor_set(v___x_1907_, 0, v___x_1925_);
v___x_1927_ = v___x_1907_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___f_1917_);
v___x_1927_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v_toApplicative_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1970_; 
v___x_1928_ = l_StateRefT_x27_instMonad___redArg(v___x_1927_);
v_toApplicative_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v___x_1928_, 1);
lean_dec(v_unused_1971_);
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1970_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_toApplicative_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1970_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_toFunctor_1933_; lean_object* v_toSeq_1934_; lean_object* v_toSeqLeft_1935_; lean_object* v_toSeqRight_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1968_; 
v_toFunctor_1933_ = lean_ctor_get(v_toApplicative_1929_, 0);
v_toSeq_1934_ = lean_ctor_get(v_toApplicative_1929_, 2);
v_toSeqLeft_1935_ = lean_ctor_get(v_toApplicative_1929_, 3);
v_toSeqRight_1936_ = lean_ctor_get(v_toApplicative_1929_, 4);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_toApplicative_1929_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v_toApplicative_1929_, 1);
lean_dec(v_unused_1969_);
v___x_1938_ = v_toApplicative_1929_;
v_isShared_1939_ = v_isSharedCheck_1968_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_toSeqRight_1936_);
lean_inc(v_toSeqLeft_1935_);
lean_inc(v_toSeq_1934_);
lean_inc(v_toFunctor_1933_);
lean_dec(v_toApplicative_1929_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1968_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___f_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; lean_object* v___f_1946_; lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___x_1956_; 
v___f_1940_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1941_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1941_, 0, v___f_1940_);
v___x_1942_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1943_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1943_, 0, v___f_1941_);
lean_closure_set(v___f_1943_, 1, v___x_1942_);
v___f_1944_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1945_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1946_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1946_, 0, v___f_1944_);
lean_closure_set(v___f_1946_, 1, v___x_1945_);
v___f_1947_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1948_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1933_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toFunctor_1933_);
v___f_1950_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1950_, 0, v_toFunctor_1933_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___f_1949_);
lean_ctor_set(v___x_1951_, 1, v___f_1950_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toSeqRight_1936_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeqLeft_1935_);
v___f_1954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1954_, 0, v_toSeq_1934_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 4, v___f_1952_);
lean_ctor_set(v___x_1938_, 3, v___f_1953_);
lean_ctor_set(v___x_1938_, 2, v___f_1954_);
lean_ctor_set(v___x_1938_, 1, v___f_1947_);
lean_ctor_set(v___x_1938_, 0, v___x_1951_);
v___x_1956_ = v___x_1938_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___f_1947_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v___f_1954_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v___f_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v___f_1952_);
v___x_1956_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 1, v___f_1948_);
lean_ctor_set(v___x_1931_, 0, v___x_1956_);
v___x_1958_ = v___x_1931_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___f_1948_);
v___x_1958_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___f_1963_; lean_object* v___x_37996__overap_1964_; lean_object* v___x_1965_; 
v___x_1959_ = l_StateRefT_x27_instMonad___redArg(v___x_1958_);
v___x_1960_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1902_, v___f_1943_, v___f_1946_, v___x_1959_);
v___x_1961_ = l_Lean_instInhabitedExpr;
v___x_1962_ = l_instInhabitedOfMonad___redArg(v___x_1960_, v___x_1961_);
v___f_1963_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1963_, 0, v___x_1962_);
v___x_37996__overap_1964_ = lean_panic_fn_borrowed(v___f_1963_, v_msg_1893_);
lean_dec_ref(v___f_1963_);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
v___x_1965_ = lean_apply_8(v___x_37996__overap_1964_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, lean_box(0));
return v___x_1965_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1893_ = stack[0].m_obj;
lean_object* v___y_1894_ = stack[1].m_obj;
lean_object* v___y_1895_ = stack[2].m_obj;
lean_object* v___y_1896_ = stack[3].m_obj;
lean_object* v___y_1897_ = stack[4].m_obj;
lean_object* v___y_1898_ = stack[5].m_obj;
lean_object* v___y_1899_ = stack[6].m_obj;
lean_object* v___y_1900_ = stack[7].m_obj;
lean_object* v_res_1978_;
v_res_1978_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
stack->m_obj
 = v_res_1978_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1988_;
}
}
lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderType_1989_, lean_object* v_binderName_1990_, uint8_t v_binderInfo_1991_, lean_object* v_body_1992_, lean_object* v_e_1993_, lean_object* v_t_1994_, lean_object* v_b_1995_){
_start:
{
size_t v___x_1996_; size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_ptr_addr(v_binderType_1989_);
v___x_1997_ = lean_ptr_addr(v_t_1994_);
v___x_1998_ = lean_usize_dec_eq(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Expr_lam___override(v_binderName_1990_, v_t_1994_, v_b_1995_, v_binderInfo_1991_);
return v___x_1999_;
}
else
{
size_t v___x_2000_; size_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = lean_ptr_addr(v_body_1992_);
v___x_2001_ = lean_ptr_addr(v_b_1995_);
v___x_2002_ = lean_usize_dec_eq(v___x_2000_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Expr_lam___override(v_binderName_1990_, v_t_1994_, v_b_1995_, v_binderInfo_1991_);
return v___x_2003_;
}
else
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1991_, v_binderInfo_1991_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Expr_lam___override(v_binderName_1990_, v_t_1994_, v_b_1995_, v_binderInfo_1991_);
return v___x_2005_;
}
else
{
lean_dec_ref(v_b_1995_);
lean_dec_ref(v_t_1994_);
lean_dec(v_binderName_1990_);
lean_inc_ref(v_e_1993_);
return v_e_1993_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_1989_ = stack[0].m_obj;
lean_object* v_binderName_1990_ = stack[1].m_obj;
uint8_t v_binderInfo_1991_ = stack[2].m_num;
lean_object* v_body_1992_ = stack[3].m_obj;
lean_object* v_e_1993_ = stack[4].m_obj;
lean_object* v_t_1994_ = stack[5].m_obj;
lean_object* v_b_1995_ = stack[6].m_obj;
lean_object* v_res_2006_;
v_res_2006_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderType_1989_, v_binderName_1990_, v_binderInfo_1991_, v_body_1992_, v_e_1993_, v_t_1994_, v_b_1995_);
stack->m_obj
 = v_res_2006_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderType_2007_, lean_object* v_binderName_2008_, lean_object* v_binderInfo_2009_, lean_object* v_body_2010_, lean_object* v_e_2011_, lean_object* v_t_2012_, lean_object* v_b_2013_){
_start:
{
uint8_t v_binderInfo_41539__boxed_2014_; lean_object* v_res_2015_; 
v_binderInfo_41539__boxed_2014_ = lean_unbox(v_binderInfo_2009_);
v_res_2015_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderType_2007_, v_binderName_2008_, v_binderInfo_41539__boxed_2014_, v_body_2010_, v_e_2011_, v_t_2012_, v_b_2013_);
lean_dec_ref(v_e_2011_);
lean_dec_ref(v_body_2010_);
lean_dec_ref(v_binderType_2007_);
return v_res_2015_;
}
}
lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderType_2016_, lean_object* v_binderName_2017_, uint8_t v_binderInfo_2018_, lean_object* v_body_2019_, lean_object* v_e_2020_, lean_object* v_t_2021_, lean_object* v_b_2022_){
_start:
{
size_t v___x_2023_; size_t v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = lean_ptr_addr(v_binderType_2016_);
v___x_2024_ = lean_ptr_addr(v_t_2021_);
v___x_2025_ = lean_usize_dec_eq(v___x_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Expr_forallE___override(v_binderName_2017_, v_t_2021_, v_b_2022_, v_binderInfo_2018_);
return v___x_2026_;
}
else
{
size_t v___x_2027_; size_t v___x_2028_; uint8_t v___x_2029_; 
v___x_2027_ = lean_ptr_addr(v_body_2019_);
v___x_2028_ = lean_ptr_addr(v_b_2022_);
v___x_2029_ = lean_usize_dec_eq(v___x_2027_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Expr_forallE___override(v_binderName_2017_, v_t_2021_, v_b_2022_, v_binderInfo_2018_);
return v___x_2030_;
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2018_, v_binderInfo_2018_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_Expr_forallE___override(v_binderName_2017_, v_t_2021_, v_b_2022_, v_binderInfo_2018_);
return v___x_2032_;
}
else
{
lean_dec_ref(v_b_2022_);
lean_dec_ref(v_t_2021_);
lean_dec(v_binderName_2017_);
lean_inc_ref(v_e_2020_);
return v_e_2020_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_2016_ = stack[0].m_obj;
lean_object* v_binderName_2017_ = stack[1].m_obj;
uint8_t v_binderInfo_2018_ = stack[2].m_num;
lean_object* v_body_2019_ = stack[3].m_obj;
lean_object* v_e_2020_ = stack[4].m_obj;
lean_object* v_t_2021_ = stack[5].m_obj;
lean_object* v_b_2022_ = stack[6].m_obj;
lean_object* v_res_2033_;
v_res_2033_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderType_2016_, v_binderName_2017_, v_binderInfo_2018_, v_body_2019_, v_e_2020_, v_t_2021_, v_b_2022_);
stack->m_obj
 = v_res_2033_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderType_2034_, lean_object* v_binderName_2035_, lean_object* v_binderInfo_2036_, lean_object* v_body_2037_, lean_object* v_e_2038_, lean_object* v_t_2039_, lean_object* v_b_2040_){
_start:
{
uint8_t v_binderInfo_41589__boxed_2041_; lean_object* v_res_2042_; 
v_binderInfo_41589__boxed_2041_ = lean_unbox(v_binderInfo_2036_);
v_res_2042_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderType_2034_, v_binderName_2035_, v_binderInfo_41589__boxed_2041_, v_body_2037_, v_e_2038_, v_t_2039_, v_b_2040_);
lean_dec_ref(v_e_2038_);
lean_dec_ref(v_body_2037_);
lean_dec_ref(v_binderType_2034_);
return v_res_2042_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_2043_, lean_object* v_type_2044_, lean_object* v_val_2045_, lean_object* v_k_2046_, uint8_t v_nondep_2047_, uint8_t v_kind_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___f_2057_; lean_object* v___x_2058_; 
lean_inc(v___y_2051_);
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2049_);
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2057_, 0, v_k_2046_);
lean_closure_set(v___f_2057_, 1, v___y_2049_);
lean_closure_set(v___f_2057_, 2, v___y_2050_);
lean_closure_set(v___f_2057_, 3, v___y_2051_);
v___x_2058_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2043_, v_type_2044_, v_val_2045_, v___f_2057_, v_nondep_2047_, v_kind_2048_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2058_) == 0)
{
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2043_ = stack[0].m_obj;
lean_object* v_type_2044_ = stack[1].m_obj;
lean_object* v_val_2045_ = stack[2].m_obj;
lean_object* v_k_2046_ = stack[3].m_obj;
uint8_t v_nondep_2047_ = stack[4].m_num;
uint8_t v_kind_2048_ = stack[5].m_num;
lean_object* v___y_2049_ = stack[6].m_obj;
lean_object* v___y_2050_ = stack[7].m_obj;
lean_object* v___y_2051_ = stack[8].m_obj;
lean_object* v___y_2052_ = stack[9].m_obj;
lean_object* v___y_2053_ = stack[10].m_obj;
lean_object* v___y_2054_ = stack[11].m_obj;
lean_object* v___y_2055_ = stack[12].m_obj;
lean_object* v_res_2067_;
v_res_2067_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2043_, v_type_2044_, v_val_2045_, v_k_2046_, v_nondep_2047_, v_kind_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
stack->m_obj
 = v_res_2067_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2068_, lean_object* v_type_2069_, lean_object* v_val_2070_, lean_object* v_k_2071_, lean_object* v_nondep_2072_, lean_object* v_kind_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v_nondep_boxed_2082_; uint8_t v_kind_boxed_2083_; lean_object* v_res_2084_; 
v_nondep_boxed_2082_ = lean_unbox(v_nondep_2072_);
v_kind_boxed_2083_ = lean_unbox(v_kind_2073_);
v_res_2084_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2068_, v_type_2069_, v_val_2070_, v_k_2071_, v_nondep_boxed_2082_, v_kind_boxed_2083_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = l_Lean_instInhabitedExpr;
v___x_2087_ = lean_panic_fn_borrowed(v___x_2086_, v_msg_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2088_, lean_object* v_x_2089_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_box(0);
return v___x_2090_;
}
else
{
lean_object* v_key_2091_; lean_object* v_value_2092_; lean_object* v_tail_2093_; uint8_t v___x_2094_; 
v_key_2091_ = lean_ctor_get(v_x_2089_, 0);
v_value_2092_ = lean_ctor_get(v_x_2089_, 1);
v_tail_2093_ = lean_ctor_get(v_x_2089_, 2);
v___x_2094_ = l_Lean_ExprStructEq_beq(v_key_2091_, v_a_2088_);
if (v___x_2094_ == 0)
{
v_x_2089_ = v_tail_2093_;
goto _start;
}
else
{
lean_object* v___x_2096_; 
lean_inc(v_value_2092_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_value_2092_);
return v___x_2096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2097_, lean_object* v_x_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2097_, v_x_2098_);
lean_dec(v_x_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_buckets_2102_; lean_object* v___x_2103_; uint64_t v___x_2104_; uint64_t v___x_2105_; uint64_t v___x_2106_; uint64_t v_fold_2107_; uint64_t v___x_2108_; uint64_t v___x_2109_; uint64_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_buckets_2102_ = lean_ctor_get(v_m_2100_, 1);
v___x_2103_ = lean_array_get_size(v_buckets_2102_);
v___x_2104_ = l_Lean_ExprStructEq_hash(v_a_2101_);
v___x_2105_ = 32ULL;
v___x_2106_ = lean_uint64_shift_right(v___x_2104_, v___x_2105_);
v_fold_2107_ = lean_uint64_xor(v___x_2104_, v___x_2106_);
v___x_2108_ = 16ULL;
v___x_2109_ = lean_uint64_shift_right(v_fold_2107_, v___x_2108_);
v___x_2110_ = lean_uint64_xor(v_fold_2107_, v___x_2109_);
v___x_2111_ = lean_uint64_to_usize(v___x_2110_);
v___x_2112_ = lean_usize_of_nat(v___x_2103_);
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_sub(v___x_2112_, v___x_2113_);
v___x_2115_ = lean_usize_land(v___x_2111_, v___x_2114_);
v___x_2116_ = lean_array_uget_borrowed(v_buckets_2102_, v___x_2115_);
v___x_2117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2101_, v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2118_, v_a_2119_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_m_2118_);
return v_res_2120_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2121_, lean_object* v_x_2122_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
uint8_t v___x_2123_; 
v___x_2123_ = 0;
return v___x_2123_;
}
else
{
lean_object* v_key_2124_; lean_object* v_tail_2125_; lean_object* v_fst_2126_; lean_object* v_snd_2127_; lean_object* v_fst_2128_; lean_object* v_snd_2129_; uint8_t v___x_2133_; 
v_key_2124_ = lean_ctor_get(v_x_2122_, 0);
v_tail_2125_ = lean_ctor_get(v_x_2122_, 2);
v_fst_2126_ = lean_ctor_get(v_key_2124_, 0);
v_snd_2127_ = lean_ctor_get(v_key_2124_, 1);
v_fst_2128_ = lean_ctor_get(v_a_2121_, 0);
v_snd_2129_ = lean_ctor_get(v_a_2121_, 1);
v___x_2133_ = lean_unbox(v_fst_2128_);
if (v___x_2133_ == 0)
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_unbox(v_fst_2126_);
if (v___x_2134_ == 0)
{
goto v___jp_2130_;
}
else
{
v_x_2122_ = v_tail_2125_;
goto _start;
}
}
else
{
uint8_t v___x_2136_; 
v___x_2136_ = lean_unbox(v_fst_2126_);
if (v___x_2136_ == 0)
{
v_x_2122_ = v_tail_2125_;
goto _start;
}
else
{
goto v___jp_2130_;
}
}
v___jp_2130_:
{
uint8_t v___x_2131_; 
v___x_2131_ = l_Lean_ExprStructEq_beq(v_snd_2127_, v_snd_2129_);
if (v___x_2131_ == 0)
{
v_x_2122_ = v_tail_2125_;
goto _start;
}
else
{
return v___x_2131_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2121_ = stack[0].m_obj;
lean_object* v_x_2122_ = stack[1].m_obj;
uint8_t v_res_2138_;
v_res_2138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2121_, v_x_2122_);
stack->m_num = v_res_2138_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2139_, lean_object* v_x_2140_){
_start:
{
uint8_t v_res_2141_; lean_object* v_r_2142_; 
v_res_2141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2139_, v_x_2140_);
lean_dec(v_x_2140_);
lean_dec_ref(v_a_2139_);
v_r_2142_ = lean_box(v_res_2141_);
return v_r_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2143_, lean_object* v_b_2144_, lean_object* v_x_2145_){
_start:
{
if (lean_obj_tag(v_x_2145_) == 0)
{
lean_dec(v_b_2144_);
lean_dec_ref(v_a_2143_);
return v_x_2145_;
}
else
{
lean_object* v_key_2146_; lean_object* v_value_2147_; lean_object* v_tail_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2167_; 
v_key_2146_ = lean_ctor_get(v_x_2145_, 0);
v_value_2147_ = lean_ctor_get(v_x_2145_, 1);
v_tail_2148_ = lean_ctor_get(v_x_2145_, 2);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_x_2145_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2150_ = v_x_2145_;
v_isShared_2151_ = v_isSharedCheck_2167_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_tail_2148_);
lean_inc(v_value_2147_);
lean_inc(v_key_2146_);
lean_dec(v_x_2145_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2167_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v_fst_2159_; lean_object* v_snd_2160_; uint8_t v___x_2164_; 
v_fst_2157_ = lean_ctor_get(v_key_2146_, 0);
v_snd_2158_ = lean_ctor_get(v_key_2146_, 1);
v_fst_2159_ = lean_ctor_get(v_a_2143_, 0);
v_snd_2160_ = lean_ctor_get(v_a_2143_, 1);
v___x_2164_ = lean_unbox(v_fst_2159_);
if (v___x_2164_ == 0)
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_unbox(v_fst_2157_);
if (v___x_2165_ == 0)
{
goto v___jp_2161_;
}
else
{
goto v___jp_2152_;
}
}
else
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_unbox(v_fst_2157_);
if (v___x_2166_ == 0)
{
goto v___jp_2152_;
}
else
{
goto v___jp_2161_;
}
}
v___jp_2152_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2143_, v_b_2144_, v_tail_2148_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 2, v___x_2153_);
v___x_2155_ = v___x_2150_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_key_2146_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_value_2147_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
v___jp_2161_:
{
uint8_t v___x_2162_; 
v___x_2162_ = l_Lean_ExprStructEq_beq(v_snd_2158_, v_snd_2160_);
if (v___x_2162_ == 0)
{
goto v___jp_2152_;
}
else
{
lean_object* v___x_2163_; 
lean_del_object(v___x_2150_);
lean_dec(v_value_2147_);
lean_dec(v_key_2146_);
v___x_2163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2163_, 0, v_a_2143_);
lean_ctor_set(v___x_2163_, 1, v_b_2144_);
lean_ctor_set(v___x_2163_, 2, v_tail_2148_);
return v___x_2163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
return v_x_2168_;
}
else
{
lean_object* v_key_2170_; lean_object* v_value_2171_; lean_object* v_tail_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2203_; 
v_key_2170_ = lean_ctor_get(v_x_2169_, 0);
v_value_2171_ = lean_ctor_get(v_x_2169_, 1);
v_tail_2172_ = lean_ctor_get(v_x_2169_, 2);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2169_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2174_ = v_x_2169_;
v_isShared_2175_ = v_isSharedCheck_2203_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_tail_2172_);
lean_inc(v_value_2171_);
lean_inc(v_key_2170_);
lean_dec(v_x_2169_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2203_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2178_; uint64_t v___y_2180_; uint8_t v___x_2200_; 
v_fst_2176_ = lean_ctor_get(v_key_2170_, 0);
v_snd_2177_ = lean_ctor_get(v_key_2170_, 1);
v___x_2178_ = lean_array_get_size(v_x_2168_);
v___x_2200_ = lean_unbox(v_fst_2176_);
if (v___x_2200_ == 0)
{
uint64_t v___x_2201_; 
v___x_2201_ = 13ULL;
v___y_2180_ = v___x_2201_;
goto v___jp_2179_;
}
else
{
uint64_t v___x_2202_; 
v___x_2202_ = 11ULL;
v___y_2180_ = v___x_2202_;
goto v___jp_2179_;
}
v___jp_2179_:
{
uint64_t v___x_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v___x_2184_; uint64_t v_fold_2185_; uint64_t v___x_2186_; uint64_t v___x_2187_; uint64_t v___x_2188_; size_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2181_ = l_Lean_ExprStructEq_hash(v_snd_2177_);
v___x_2182_ = lean_uint64_mix_hash(v___y_2180_, v___x_2181_);
v___x_2183_ = 32ULL;
v___x_2184_ = lean_uint64_shift_right(v___x_2182_, v___x_2183_);
v_fold_2185_ = lean_uint64_xor(v___x_2182_, v___x_2184_);
v___x_2186_ = 16ULL;
v___x_2187_ = lean_uint64_shift_right(v_fold_2185_, v___x_2186_);
v___x_2188_ = lean_uint64_xor(v_fold_2185_, v___x_2187_);
v___x_2189_ = lean_uint64_to_usize(v___x_2188_);
v___x_2190_ = lean_usize_of_nat(v___x_2178_);
v___x_2191_ = ((size_t)1ULL);
v___x_2192_ = lean_usize_sub(v___x_2190_, v___x_2191_);
v___x_2193_ = lean_usize_land(v___x_2189_, v___x_2192_);
v___x_2194_ = lean_array_uget_borrowed(v_x_2168_, v___x_2193_);
lean_inc(v___x_2194_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 2, v___x_2194_);
v___x_2196_ = v___x_2174_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_key_2170_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_value_2171_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_array_uset(v_x_2168_, v___x_2193_, v___x_2196_);
v_x_2168_ = v___x_2197_;
v_x_2169_ = v_tail_2172_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2204_, lean_object* v_source_2205_, lean_object* v_target_2206_){
_start:
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_array_get_size(v_source_2205_);
v___x_2208_ = lean_nat_dec_lt(v_i_2204_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_dec_ref(v_source_2205_);
lean_dec(v_i_2204_);
return v_target_2206_;
}
else
{
lean_object* v_es_2209_; lean_object* v___x_2210_; lean_object* v_source_2211_; lean_object* v_target_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_es_2209_ = lean_array_fget(v_source_2205_, v_i_2204_);
v___x_2210_ = lean_box(0);
v_source_2211_ = lean_array_fset(v_source_2205_, v_i_2204_, v___x_2210_);
v_target_2212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2206_, v_es_2209_);
v___x_2213_ = lean_unsigned_to_nat(1u);
v___x_2214_ = lean_nat_add(v_i_2204_, v___x_2213_);
lean_dec(v_i_2204_);
v_i_2204_ = v___x_2214_;
v_source_2205_ = v_source_2211_;
v_target_2206_ = v_target_2212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2216_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_nbuckets_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2217_ = lean_array_get_size(v_data_2216_);
v___x_2218_ = lean_unsigned_to_nat(2u);
v_nbuckets_2219_ = lean_nat_mul(v___x_2217_, v___x_2218_);
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_mk_array(v_nbuckets_2219_, v___x_2221_);
v___x_2223_ = lean_array_propagate_mark(v_data_2216_, v___x_2222_);
v___x_2224_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2220_, v_data_2216_, v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2225_, lean_object* v_a_2226_, lean_object* v_b_2227_){
_start:
{
lean_object* v_size_2228_; lean_object* v_buckets_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2280_; 
v_size_2228_ = lean_ctor_get(v_m_2225_, 0);
v_buckets_2229_ = lean_ctor_get(v_m_2225_, 1);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_m_2225_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2231_ = v_m_2225_;
v_isShared_2232_ = v_isSharedCheck_2280_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_buckets_2229_);
lean_inc(v_size_2228_);
lean_dec(v_m_2225_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2280_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2235_; uint64_t v___y_2237_; uint8_t v___x_2277_; 
v_fst_2233_ = lean_ctor_get(v_a_2226_, 0);
v_snd_2234_ = lean_ctor_get(v_a_2226_, 1);
v___x_2235_ = lean_array_get_size(v_buckets_2229_);
v___x_2277_ = lean_unbox(v_fst_2233_);
if (v___x_2277_ == 0)
{
uint64_t v___x_2278_; 
v___x_2278_ = 13ULL;
v___y_2237_ = v___x_2278_;
goto v___jp_2236_;
}
else
{
uint64_t v___x_2279_; 
v___x_2279_ = 11ULL;
v___y_2237_ = v___x_2279_;
goto v___jp_2236_;
}
v___jp_2236_:
{
uint64_t v___x_2238_; uint64_t v___x_2239_; uint64_t v___x_2240_; uint64_t v___x_2241_; uint64_t v_fold_2242_; uint64_t v___x_2243_; uint64_t v___x_2244_; uint64_t v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; size_t v___x_2250_; lean_object* v_bkt_2251_; uint8_t v___x_2252_; 
v___x_2238_ = l_Lean_ExprStructEq_hash(v_snd_2234_);
v___x_2239_ = lean_uint64_mix_hash(v___y_2237_, v___x_2238_);
v___x_2240_ = 32ULL;
v___x_2241_ = lean_uint64_shift_right(v___x_2239_, v___x_2240_);
v_fold_2242_ = lean_uint64_xor(v___x_2239_, v___x_2241_);
v___x_2243_ = 16ULL;
v___x_2244_ = lean_uint64_shift_right(v_fold_2242_, v___x_2243_);
v___x_2245_ = lean_uint64_xor(v_fold_2242_, v___x_2244_);
v___x_2246_ = lean_uint64_to_usize(v___x_2245_);
v___x_2247_ = lean_usize_of_nat(v___x_2235_);
v___x_2248_ = ((size_t)1ULL);
v___x_2249_ = lean_usize_sub(v___x_2247_, v___x_2248_);
v___x_2250_ = lean_usize_land(v___x_2246_, v___x_2249_);
v_bkt_2251_ = lean_array_uget_borrowed(v_buckets_2229_, v___x_2250_);
v___x_2252_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2226_, v_bkt_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v_size_x27_2254_; lean_object* v___x_2255_; lean_object* v_buckets_x27_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2253_ = lean_unsigned_to_nat(1u);
v_size_x27_2254_ = lean_nat_add(v_size_2228_, v___x_2253_);
lean_dec(v_size_2228_);
lean_inc(v_bkt_2251_);
v___x_2255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2255_, 0, v_a_2226_);
lean_ctor_set(v___x_2255_, 1, v_b_2227_);
lean_ctor_set(v___x_2255_, 2, v_bkt_2251_);
v_buckets_x27_2256_ = lean_array_uset(v_buckets_2229_, v___x_2250_, v___x_2255_);
v___x_2257_ = lean_unsigned_to_nat(4u);
v___x_2258_ = lean_nat_mul(v_size_x27_2254_, v___x_2257_);
v___x_2259_ = lean_unsigned_to_nat(3u);
v___x_2260_ = lean_nat_div(v___x_2258_, v___x_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_array_get_size(v_buckets_x27_2256_);
v___x_2262_ = lean_nat_dec_le(v___x_2260_, v___x_2261_);
lean_dec(v___x_2260_);
if (v___x_2262_ == 0)
{
lean_object* v_val_2263_; lean_object* v___x_2265_; 
v_val_2263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2256_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v_val_2263_);
lean_ctor_set(v___x_2231_, 0, v_size_x27_2254_);
v___x_2265_ = v___x_2231_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_size_x27_2254_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_val_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
else
{
lean_object* v___x_2268_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v_buckets_x27_2256_);
lean_ctor_set(v___x_2231_, 0, v_size_x27_2254_);
v___x_2268_ = v___x_2231_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_size_x27_2254_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_buckets_x27_2256_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
else
{
lean_object* v___x_2270_; lean_object* v_buckets_x27_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
lean_inc(v_bkt_2251_);
v___x_2270_ = lean_box(0);
v_buckets_x27_2271_ = lean_array_uset(v_buckets_2229_, v___x_2250_, v___x_2270_);
v___x_2272_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2226_, v_b_2227_, v_bkt_2251_);
v___x_2273_ = lean_array_uset(v_buckets_x27_2271_, v___x_2250_, v___x_2272_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2273_);
v___x_2275_ = v___x_2231_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_size_2228_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2281_, lean_object* v_x_2282_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 0)
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_box(0);
return v___x_2283_;
}
else
{
lean_object* v_key_2284_; lean_object* v_value_2285_; lean_object* v_tail_2286_; lean_object* v_fst_2287_; lean_object* v_snd_2288_; lean_object* v_fst_2289_; lean_object* v_snd_2290_; uint8_t v___x_2295_; 
v_key_2284_ = lean_ctor_get(v_x_2282_, 0);
v_value_2285_ = lean_ctor_get(v_x_2282_, 1);
v_tail_2286_ = lean_ctor_get(v_x_2282_, 2);
v_fst_2287_ = lean_ctor_get(v_key_2284_, 0);
v_snd_2288_ = lean_ctor_get(v_key_2284_, 1);
v_fst_2289_ = lean_ctor_get(v_a_2281_, 0);
v_snd_2290_ = lean_ctor_get(v_a_2281_, 1);
v___x_2295_ = lean_unbox(v_fst_2289_);
if (v___x_2295_ == 0)
{
uint8_t v___x_2296_; 
v___x_2296_ = lean_unbox(v_fst_2287_);
if (v___x_2296_ == 0)
{
goto v___jp_2291_;
}
else
{
v_x_2282_ = v_tail_2286_;
goto _start;
}
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_unbox(v_fst_2287_);
if (v___x_2298_ == 0)
{
v_x_2282_ = v_tail_2286_;
goto _start;
}
else
{
goto v___jp_2291_;
}
}
v___jp_2291_:
{
uint8_t v___x_2292_; 
v___x_2292_ = l_Lean_ExprStructEq_beq(v_snd_2288_, v_snd_2290_);
if (v___x_2292_ == 0)
{
v_x_2282_ = v_tail_2286_;
goto _start;
}
else
{
lean_object* v___x_2294_; 
lean_inc(v_value_2285_);
v___x_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2294_, 0, v_value_2285_);
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2300_, lean_object* v_x_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2300_, v_x_2301_);
lean_dec(v_x_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_buckets_2305_; lean_object* v_fst_2306_; lean_object* v_snd_2307_; lean_object* v___x_2308_; uint64_t v___y_2310_; uint8_t v___x_2326_; 
v_buckets_2305_ = lean_ctor_get(v_m_2303_, 1);
v_fst_2306_ = lean_ctor_get(v_a_2304_, 0);
v_snd_2307_ = lean_ctor_get(v_a_2304_, 1);
v___x_2308_ = lean_array_get_size(v_buckets_2305_);
v___x_2326_ = lean_unbox(v_fst_2306_);
if (v___x_2326_ == 0)
{
uint64_t v___x_2327_; 
v___x_2327_ = 13ULL;
v___y_2310_ = v___x_2327_;
goto v___jp_2309_;
}
else
{
uint64_t v___x_2328_; 
v___x_2328_ = 11ULL;
v___y_2310_ = v___x_2328_;
goto v___jp_2309_;
}
v___jp_2309_:
{
uint64_t v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v_fold_2315_; uint64_t v___x_2316_; uint64_t v___x_2317_; uint64_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2311_ = l_Lean_ExprStructEq_hash(v_snd_2307_);
v___x_2312_ = lean_uint64_mix_hash(v___y_2310_, v___x_2311_);
v___x_2313_ = 32ULL;
v___x_2314_ = lean_uint64_shift_right(v___x_2312_, v___x_2313_);
v_fold_2315_ = lean_uint64_xor(v___x_2312_, v___x_2314_);
v___x_2316_ = 16ULL;
v___x_2317_ = lean_uint64_shift_right(v_fold_2315_, v___x_2316_);
v___x_2318_ = lean_uint64_xor(v_fold_2315_, v___x_2317_);
v___x_2319_ = lean_uint64_to_usize(v___x_2318_);
v___x_2320_ = lean_usize_of_nat(v___x_2308_);
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_sub(v___x_2320_, v___x_2321_);
v___x_2323_ = lean_usize_land(v___x_2319_, v___x_2322_);
v___x_2324_ = lean_array_uget_borrowed(v_buckets_2305_, v___x_2323_);
v___x_2325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2304_, v___x_2324_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2329_, v_a_2330_);
lean_dec_ref(v_a_2330_);
lean_dec_ref(v_m_2329_);
return v_res_2331_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2332_; lean_object* v_dummy_2333_; 
v___x_2332_ = lean_box(0);
v_dummy_2333_ = l_Lean_Expr_sort___override(v___x_2332_);
return v_dummy_2333_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2334_, lean_object* v_fst_2335_, lean_object* v_fvars_2336_, lean_object* v_a_2337_, lean_object* v_b_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_a_2348_; uint8_t v___x_2352_; 
v___x_2352_ = lean_nat_dec_lt(v_a_2337_, v_upperBound_2334_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v_a_2337_);
lean_dec(v_fvars_2336_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_b_2338_);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v_binderInfo_2356_; uint8_t v___x_2357_; 
v___x_2354_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2355_ = lean_array_get_borrowed(v___x_2354_, v_fst_2335_, v_a_2337_);
v_binderInfo_2356_ = lean_ctor_get_uint8(v___x_2355_, sizeof(void*)*2);
v___x_2357_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2356_);
if (v___x_2357_ == 0)
{
v_a_2348_ = v_b_2338_;
goto v___jp_2347_;
}
else
{
lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2358_ = l_Lean_instInhabitedExpr;
v___x_2359_ = 0;
v___x_2360_ = lean_array_get_borrowed(v___x_2358_, v_b_2338_, v_a_2337_);
lean_inc(v___x_2360_);
lean_inc(v_fvars_2336_);
v___x_2361_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2336_, v___x_2360_, v___x_2359_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = lean_array_set(v_b_2338_, v_a_2337_, v_a_2362_);
v_a_2348_ = v___x_2363_;
goto v___jp_2347_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v_b_2338_);
lean_dec(v_a_2337_);
lean_dec(v_fvars_2336_);
v_a_2364_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2361_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2361_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
v___jp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_add(v_a_2337_, v___x_2349_);
lean_dec(v_a_2337_);
v_a_2337_ = v___x_2350_;
v_b_2338_ = v_a_2348_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2334_ = stack[0].m_obj;
lean_object* v_fst_2335_ = stack[1].m_obj;
lean_object* v_fvars_2336_ = stack[2].m_obj;
lean_object* v_a_2337_ = stack[3].m_obj;
lean_object* v_b_2338_ = stack[4].m_obj;
lean_object* v___y_2339_ = stack[5].m_obj;
lean_object* v___y_2340_ = stack[6].m_obj;
lean_object* v___y_2341_ = stack[7].m_obj;
lean_object* v___y_2342_ = stack[8].m_obj;
lean_object* v___y_2343_ = stack[9].m_obj;
lean_object* v___y_2344_ = stack[10].m_obj;
lean_object* v___y_2345_ = stack[11].m_obj;
lean_object* v_res_2372_;
v_res_2372_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_2334_, v_fst_2335_, v_fvars_2336_, v_a_2337_, v_b_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
stack->m_obj
 = v_res_2372_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2373_, size_t v_sz_2374_, size_t v_i_2375_, lean_object* v_bs_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_usize_dec_lt(v_i_2375_, v_sz_2374_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
lean_dec(v_fvars_2373_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_bs_2376_);
return v___x_2386_;
}
else
{
uint8_t v___x_2387_; lean_object* v_v_2388_; lean_object* v___x_2389_; lean_object* v_bs_x27_2390_; lean_object* v___x_2391_; 
v___x_2387_ = 0;
v_v_2388_ = lean_array_uget(v_bs_2376_, v_i_2375_);
v___x_2389_ = lean_unsigned_to_nat(0u);
v_bs_x27_2390_ = lean_array_uset(v_bs_2376_, v_i_2375_, v___x_2389_);
lean_inc(v_fvars_2373_);
v___x_2391_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2373_, v_v_2388_, v___x_2387_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; size_t v___x_2393_; size_t v___x_2394_; lean_object* v___x_2395_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_add(v_i_2375_, v___x_2393_);
v___x_2395_ = lean_array_uset(v_bs_x27_2390_, v_i_2375_, v_a_2392_);
v_i_2375_ = v___x_2394_;
v_bs_2376_ = v___x_2395_;
goto _start;
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_bs_x27_2390_);
lean_dec(v_fvars_2373_);
v_a_2397_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2391_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2391_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2373_ = stack[0].m_obj;
size_t v_sz_2374_ = stack[1].m_num;
size_t v_i_2375_ = stack[2].m_num;
lean_object* v_bs_2376_ = stack[3].m_obj;
lean_object* v___y_2377_ = stack[4].m_obj;
lean_object* v___y_2378_ = stack[5].m_obj;
lean_object* v___y_2379_ = stack[6].m_obj;
lean_object* v___y_2380_ = stack[7].m_obj;
lean_object* v___y_2381_ = stack[8].m_obj;
lean_object* v___y_2382_ = stack[9].m_obj;
lean_object* v___y_2383_ = stack[10].m_obj;
lean_object* v_res_2405_;
v_res_2405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2373_, v_sz_2374_, v_i_2375_, v_bs_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
stack->m_obj
 = v_res_2405_;
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2406_, lean_object* v_f_2407_, lean_object* v_args_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
uint8_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = 0;
lean_inc_ref(v_f_2407_);
lean_inc(v_fvars_2406_);
v___x_2418_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2406_, v_f_2407_, v___x_2417_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
if (lean_obj_tag(v___x_2418_) == 0)
{
uint8_t v_implicits_2419_; 
v_implicits_2419_ = lean_ctor_get_uint8(v_a_2409_, 2);
if (v_implicits_2419_ == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2418_, 1);
lean_inc(v_a_2415_);
lean_inc_ref(v_a_2414_);
lean_inc(v_a_2413_);
lean_inc_ref(v_a_2412_);
v___x_2421_ = lean_infer_type(v_f_2407_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2422_, v_args_2408_, v___x_2417_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v_fst_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v_fst_2425_ = lean_ctor_get(v_a_2424_, 0);
lean_inc(v_fst_2425_);
lean_dec(v_a_2424_);
v___x_2426_ = lean_array_get_size(v_args_2408_);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2426_, v_fst_2425_, v_fvars_2406_, v___x_2427_, v_args_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_fst_2425_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2437_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = l_Lean_mkAppN(v_a_2420_, v_a_2429_);
lean_dec(v_a_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v_a_2420_);
v_a_2438_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2428_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2428_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_a_2420_);
lean_dec_ref(v_args_2408_);
lean_dec(v_fvars_2406_);
v_a_2446_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2423_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2423_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_dec(v_a_2420_);
lean_dec_ref(v_args_2408_);
lean_dec(v_fvars_2406_);
return v___x_2421_;
}
}
else
{
lean_object* v_a_2454_; size_t v_sz_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
lean_dec_ref(v_f_2407_);
v_a_2454_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2418_, 1);
v_sz_2455_ = lean_array_size(v_args_2408_);
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2406_, v_sz_2455_, v___x_2456_, v_args_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2466_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = l_Lean_mkAppN(v_a_2454_, v_a_2458_);
lean_dec(v_a_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2464_ = v___x_2460_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_a_2454_);
v_a_2467_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2457_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2457_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2408_);
lean_dec_ref(v_f_2407_);
lean_dec(v_fvars_2406_);
return v___x_2418_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2406_ = stack[0].m_obj;
lean_object* v_f_2407_ = stack[1].m_obj;
lean_object* v_args_2408_ = stack[2].m_obj;
lean_object* v_a_2409_ = stack[3].m_obj;
lean_object* v_a_2410_ = stack[4].m_obj;
lean_object* v_a_2411_ = stack[5].m_obj;
lean_object* v_a_2412_ = stack[6].m_obj;
lean_object* v_a_2413_ = stack[7].m_obj;
lean_object* v_a_2414_ = stack[8].m_obj;
lean_object* v_a_2415_ = stack[9].m_obj;
lean_object* v_res_2475_;
v_res_2475_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2406_, v_f_2407_, v_args_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
stack->m_obj
 = v_res_2475_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2476_, lean_object* v_f_2477_, lean_object* v_args_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2476_, v_f_2477_, v_args_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
return v_res_2487_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2488_, lean_object* v_b_2489_, uint8_t v___x_2490_, lean_object* v_mk_2491_, lean_object* v_a_2492_, lean_object* v_x_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_inc_ref(v_x_2493_);
v___x_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_x_2493_);
lean_ctor_set(v___x_2502_, 1, v_fvars_2488_);
v___x_2503_ = lean_expr_instantiate1(v_b_2489_, v_x_2493_);
v___x_2504_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2502_, v___x_2503_, v___x_2490_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2504_) == 0)
{
uint8_t v_lift_2505_; 
v_lift_2505_ = lean_ctor_get_uint8(v___y_2494_, 10);
if (v_lift_2505_ == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2518_; 
v_a_2506_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2508_ = v___x_2504_;
v_isShared_2509_ = v_isSharedCheck_2518_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2504_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2518_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2510_ = lean_unsigned_to_nat(1u);
v___x_2511_ = lean_mk_empty_array_with_capacity(v___x_2510_);
v___x_2512_ = lean_array_push(v___x_2511_, v_x_2493_);
v___x_2513_ = lean_expr_abstract(v_a_2506_, v___x_2512_);
lean_dec_ref(v___x_2512_);
lean_dec(v_a_2506_);
v___x_2514_ = lean_apply_2(v_mk_2491_, v_a_2492_, v___x_2513_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2514_);
v___x_2516_ = v___x_2508_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_a_2519_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2520_ = l_Lean_Expr_fvarId_x21(v_x_2493_);
v___x_2521_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2520_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2535_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2535_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2535_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2526_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2522_, v_a_2519_);
lean_dec(v_a_2522_);
v___x_2527_ = lean_unsigned_to_nat(1u);
v___x_2528_ = lean_mk_empty_array_with_capacity(v___x_2527_);
v___x_2529_ = lean_array_push(v___x_2528_, v_x_2493_);
v___x_2530_ = lean_expr_abstract(v___x_2526_, v___x_2529_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2526_);
v___x_2531_ = lean_apply_2(v_mk_2491_, v_a_2492_, v___x_2530_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2531_);
v___x_2533_ = v___x_2524_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_x_2493_);
lean_dec_ref(v_a_2492_);
lean_dec_ref(v_mk_2491_);
v_a_2536_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2521_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2521_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2493_);
lean_dec_ref(v_a_2492_);
lean_dec_ref(v_mk_2491_);
return v___x_2504_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2488_ = stack[0].m_obj;
lean_object* v_b_2489_ = stack[1].m_obj;
uint8_t v___x_2490_ = stack[2].m_num;
lean_object* v_mk_2491_ = stack[3].m_obj;
lean_object* v_a_2492_ = stack[4].m_obj;
lean_object* v_x_2493_ = stack[5].m_obj;
lean_object* v___y_2494_ = stack[6].m_obj;
lean_object* v___y_2495_ = stack[7].m_obj;
lean_object* v___y_2496_ = stack[8].m_obj;
lean_object* v___y_2497_ = stack[9].m_obj;
lean_object* v___y_2498_ = stack[10].m_obj;
lean_object* v___y_2499_ = stack[11].m_obj;
lean_object* v___y_2500_ = stack[12].m_obj;
lean_object* v_res_2544_;
v_res_2544_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2488_, v_b_2489_, v___x_2490_, v_mk_2491_, v_a_2492_, v_x_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
stack->m_obj
 = v_res_2544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2545_, lean_object* v_b_2546_, lean_object* v___x_2547_, lean_object* v_mk_2548_, lean_object* v_a_2549_, lean_object* v_x_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v___x_42426__boxed_2559_; lean_object* v_res_2560_; 
v___x_42426__boxed_2559_ = lean_unbox(v___x_2547_);
v_res_2560_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2545_, v_b_2546_, v___x_42426__boxed_2559_, v_mk_2548_, v_a_2549_, v_x_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec_ref(v_b_2546_);
return v_res_2560_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2561_, lean_object* v_n_2562_, lean_object* v_t_2563_, lean_object* v_b_2564_, uint8_t v_i_2565_, lean_object* v_mk_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
uint8_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = 0;
lean_inc(v_fvars_2561_);
v___x_2576_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2561_, v_t_2563_, v___x_2575_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
if (lean_obj_tag(v___x_2576_) == 0)
{
uint8_t v_underBinder_2577_; 
v_underBinder_2577_ = lean_ctor_get_uint8(v_a_2567_, 4);
if (v_underBinder_2577_ == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_n_2562_);
lean_dec(v_fvars_2561_);
v_a_2578_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2580_ = v___x_2576_;
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2576_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2582_ = lean_apply_2(v_mk_2566_, v_a_2578_, v_b_2564_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2582_);
v___x_2584_ = v___x_2580_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2588_; lean_object* v___f_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; 
v_a_2587_ = lean_ctor_get(v___x_2576_, 0);
lean_inc_n(v_a_2587_, 2);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2588_ = lean_box(v___x_2575_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2589_, 0, v_fvars_2561_);
lean_closure_set(v___f_2589_, 1, v_b_2564_);
lean_closure_set(v___f_2589_, 2, v___x_2588_);
lean_closure_set(v___f_2589_, 3, v_mk_2566_);
lean_closure_set(v___f_2589_, 4, v_a_2587_);
v___x_2590_ = 0;
v___x_2591_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2562_, v_i_2565_, v_a_2587_, v___f_2589_, v___x_2590_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
return v___x_2591_;
}
}
else
{
lean_dec_ref(v_mk_2566_);
lean_dec_ref(v_b_2564_);
lean_dec(v_n_2562_);
lean_dec(v_fvars_2561_);
return v___x_2576_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2561_ = stack[0].m_obj;
lean_object* v_n_2562_ = stack[1].m_obj;
lean_object* v_t_2563_ = stack[2].m_obj;
lean_object* v_b_2564_ = stack[3].m_obj;
uint8_t v_i_2565_ = stack[4].m_num;
lean_object* v_mk_2566_ = stack[5].m_obj;
lean_object* v_a_2567_ = stack[6].m_obj;
lean_object* v_a_2568_ = stack[7].m_obj;
lean_object* v_a_2569_ = stack[8].m_obj;
lean_object* v_a_2570_ = stack[9].m_obj;
lean_object* v_a_2571_ = stack[10].m_obj;
lean_object* v_a_2572_ = stack[11].m_obj;
lean_object* v_a_2573_ = stack[12].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2561_, v_n_2562_, v_t_2563_, v_b_2564_, v_i_2565_, v_mk_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2593_, lean_object* v_n_2594_, lean_object* v_t_2595_, lean_object* v_b_2596_, lean_object* v_i_2597_, lean_object* v_mk_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
uint8_t v_i_boxed_2607_; lean_object* v_res_2608_; 
v_i_boxed_2607_ = lean_unbox(v_i_2597_);
v_res_2608_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2593_, v_n_2594_, v_t_2595_, v_b_2596_, v_i_boxed_2607_, v_mk_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2609_, lean_object* v_e_2610_, lean_object* v_topLevel_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
uint8_t v_topLevel_boxed_2620_; lean_object* v_res_2621_; 
v_topLevel_boxed_2620_ = lean_unbox(v_topLevel_2611_);
v_res_2621_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2609_, v_e_2610_, v_topLevel_boxed_2620_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
return v_res_2621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2626_ = lean_unsigned_to_nat(27u);
v___x_2627_ = lean_unsigned_to_nat(1981u);
v___x_2628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2630_ = l_mkPanicMessageWithDecl(v___x_2629_, v___x_2628_, v___x_2627_, v___x_2626_, v___x_2625_);
return v___x_2630_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2631_, lean_object* v_fvars_2632_, lean_object* v_b_2633_, uint8_t v___x_2634_, lean_object* v_e_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, uint8_t v_isLet_2638_, uint8_t v_topLevel_2639_, lean_object* v_x_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
if (v_fst_2631_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_inc_ref(v_x_2640_);
v___x_2649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2649_, 0, v_x_2640_);
lean_ctor_set(v___x_2649_, 1, v_fvars_2632_);
v___x_2650_ = lean_expr_instantiate1(v_b_2633_, v_x_2640_);
v___x_2651_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2649_, v___x_2650_, v___x_2634_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2651_) == 0)
{
if (lean_obj_tag(v_e_2635_) == 8)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2689_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2689_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2689_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v_declName_2656_; lean_object* v_type_2657_; lean_object* v_value_2658_; lean_object* v_body_2659_; uint8_t v_nondep_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; size_t v___x_2665_; size_t v___x_2666_; uint8_t v___x_2667_; 
v_declName_2656_ = lean_ctor_get(v_e_2635_, 0);
v_type_2657_ = lean_ctor_get(v_e_2635_, 1);
v_value_2658_ = lean_ctor_get(v_e_2635_, 2);
v_body_2659_ = lean_ctor_get(v_e_2635_, 3);
v_nondep_2660_ = lean_ctor_get_uint8(v_e_2635_, sizeof(void*)*4 + 8);
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_mk_empty_array_with_capacity(v___x_2661_);
v___x_2663_ = lean_array_push(v___x_2662_, v_x_2640_);
v___x_2664_ = lean_expr_abstract(v_a_2652_, v___x_2663_);
lean_dec_ref(v___x_2663_);
lean_dec(v_a_2652_);
v___x_2665_ = lean_ptr_addr(v_type_2657_);
v___x_2666_ = lean_ptr_addr(v_a_2636_);
v___x_2667_ = lean_usize_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_inc(v_declName_2656_);
lean_dec_ref_known(v_e_2635_, 4);
v___x_2668_ = l_Lean_Expr_letE___override(v_declName_2656_, v_a_2636_, v_a_2637_, v___x_2664_, v_nondep_2660_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2668_);
v___x_2670_ = v___x_2654_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
else
{
size_t v___x_2672_; size_t v___x_2673_; uint8_t v___x_2674_; 
v___x_2672_ = lean_ptr_addr(v_value_2658_);
v___x_2673_ = lean_ptr_addr(v_a_2637_);
v___x_2674_ = lean_usize_dec_eq(v___x_2672_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
lean_inc(v_declName_2656_);
lean_dec_ref_known(v_e_2635_, 4);
v___x_2675_ = l_Lean_Expr_letE___override(v_declName_2656_, v_a_2636_, v_a_2637_, v___x_2664_, v_nondep_2660_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2675_);
v___x_2677_ = v___x_2654_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
else
{
size_t v___x_2679_; size_t v___x_2680_; uint8_t v___x_2681_; 
v___x_2679_ = lean_ptr_addr(v_body_2659_);
v___x_2680_ = lean_ptr_addr(v___x_2664_);
v___x_2681_ = lean_usize_dec_eq(v___x_2679_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_inc(v_declName_2656_);
lean_dec_ref_known(v_e_2635_, 4);
v___x_2682_ = l_Lean_Expr_letE___override(v_declName_2656_, v_a_2636_, v_a_2637_, v___x_2664_, v_nondep_2660_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2682_);
v___x_2684_ = v___x_2654_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2687_; 
lean_dec_ref(v___x_2664_);
lean_dec_ref(v_a_2637_);
lean_dec_ref(v_a_2636_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v_e_2635_);
v___x_2687_ = v___x_2654_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_e_2635_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
else
{
lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref(v_x_2640_);
lean_dec_ref(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec_ref(v_e_2635_);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2651_, 0);
lean_dec(v_unused_2699_);
v___x_2691_ = v___x_2651_;
v_isShared_2692_ = v_isSharedCheck_2698_;
goto v_resetjp_2690_;
}
else
{
lean_dec(v___x_2651_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2698_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2694_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2693_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2694_);
v___x_2696_ = v___x_2691_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_dec_ref(v_x_2640_);
lean_dec_ref(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec_ref(v_e_2635_);
return v___x_2651_;
}
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec_ref(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec_ref(v_e_2635_);
v___x_2700_ = l_Lean_Expr_fvarId_x21(v_x_2640_);
v___x_2701_ = l_Lean_FVarId_getDecl___redArg(v___x_2700_, v___y_2644_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2702_, v_isLet_2638_, v___y_2641_, v___y_2643_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec_ref_known(v___x_2703_, 1);
v___x_2704_ = lean_expr_instantiate1(v_b_2633_, v_x_2640_);
lean_dec_ref(v_x_2640_);
v___x_2705_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2632_, v___x_2704_, v_topLevel_2639_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2705_;
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_x_2640_);
lean_dec(v_fvars_2632_);
v_a_2706_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2703_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2703_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec_ref(v_x_2640_);
lean_dec(v_fvars_2632_);
v_a_2714_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2701_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2701_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fst_2631_ = stack[0].m_num;
lean_object* v_fvars_2632_ = stack[1].m_obj;
lean_object* v_b_2633_ = stack[2].m_obj;
uint8_t v___x_2634_ = stack[3].m_num;
lean_object* v_e_2635_ = stack[4].m_obj;
lean_object* v_a_2636_ = stack[5].m_obj;
lean_object* v_a_2637_ = stack[6].m_obj;
uint8_t v_isLet_2638_ = stack[7].m_num;
uint8_t v_topLevel_2639_ = stack[8].m_num;
lean_object* v_x_2640_ = stack[9].m_obj;
lean_object* v___y_2641_ = stack[10].m_obj;
lean_object* v___y_2642_ = stack[11].m_obj;
lean_object* v___y_2643_ = stack[12].m_obj;
lean_object* v___y_2644_ = stack[13].m_obj;
lean_object* v___y_2645_ = stack[14].m_obj;
lean_object* v___y_2646_ = stack[15].m_obj;
lean_object* v___y_2647_ = stack[16].m_obj;
lean_object* v_res_2722_;
v_res_2722_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_2631_, v_fvars_2632_, v_b_2633_, v___x_2634_, v_e_2635_, v_a_2636_, v_a_2637_, v_isLet_2638_, v_topLevel_2639_, v_x_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
stack->m_obj
 = v_res_2722_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2723_ = _args[0];
lean_object* v_fvars_2724_ = _args[1];
lean_object* v_b_2725_ = _args[2];
lean_object* v___x_2726_ = _args[3];
lean_object* v_e_2727_ = _args[4];
lean_object* v_a_2728_ = _args[5];
lean_object* v_a_2729_ = _args[6];
lean_object* v_isLet_2730_ = _args[7];
lean_object* v_topLevel_2731_ = _args[8];
lean_object* v_x_2732_ = _args[9];
lean_object* v___y_2733_ = _args[10];
lean_object* v___y_2734_ = _args[11];
lean_object* v___y_2735_ = _args[12];
lean_object* v___y_2736_ = _args[13];
lean_object* v___y_2737_ = _args[14];
lean_object* v___y_2738_ = _args[15];
lean_object* v___y_2739_ = _args[16];
lean_object* v___y_2740_ = _args[17];
_start:
{
uint8_t v_fst_42571__boxed_2741_; uint8_t v___x_42572__boxed_2742_; uint8_t v_isLet_boxed_2743_; uint8_t v_topLevel_boxed_2744_; lean_object* v_res_2745_; 
v_fst_42571__boxed_2741_ = lean_unbox(v_fst_2723_);
v___x_42572__boxed_2742_ = lean_unbox(v___x_2726_);
v_isLet_boxed_2743_ = lean_unbox(v_isLet_2730_);
v_topLevel_boxed_2744_ = lean_unbox(v_topLevel_2731_);
v_res_2745_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_42571__boxed_2741_, v_fvars_2724_, v_b_2725_, v___x_42572__boxed_2742_, v_e_2727_, v_a_2728_, v_a_2729_, v_isLet_boxed_2743_, v_topLevel_boxed_2744_, v_x_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_b_2725_);
return v_res_2745_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2746_, lean_object* v_e_2747_, uint8_t v_isLet_2748_, lean_object* v_n_2749_, lean_object* v_t_2750_, lean_object* v_v_2751_, lean_object* v_b_2752_, uint8_t v_topLevel_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; uint8_t v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = 0;
lean_inc(v_fvars_2746_);
v___x_2777_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2746_, v_t_2750_, v___x_2776_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
lean_inc(v_fvars_2746_);
v___x_2779_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2746_, v_v_2751_, v___x_2776_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2891_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2891_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2891_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; uint8_t v_descend_2831_; uint8_t v_underBinder_2832_; uint8_t v_usedOnly_2833_; uint8_t v_merge_2834_; uint8_t v_lift_2835_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; uint8_t v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2873_; 
v_descend_2831_ = lean_ctor_get_uint8(v_a_2754_, 3);
v_underBinder_2832_ = lean_ctor_get_uint8(v_a_2754_, 4);
v_usedOnly_2833_ = lean_ctor_get_uint8(v_a_2754_, 5);
v_merge_2834_ = lean_ctor_get_uint8(v_a_2754_, 6);
v_lift_2835_ = lean_ctor_get_uint8(v_a_2754_, 10);
if (v_usedOnly_2833_ == 0)
{
v___y_2873_ = v___x_2776_;
goto v___jp_2872_;
}
else
{
uint8_t v___x_2889_; 
v___x_2889_ = l_Lean_Expr_hasLooseBVars(v_b_2752_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_del_object(v___x_2782_);
lean_dec(v_a_2780_);
lean_dec(v_a_2778_);
lean_dec(v_n_2749_);
lean_dec_ref(v_e_2747_);
v___x_2890_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2746_, v_b_2752_, v_topLevel_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
return v___x_2890_;
}
else
{
v___y_2873_ = v___x_2776_;
goto v___jp_2872_;
}
}
v___jp_2784_:
{
if (lean_obj_tag(v_e_2747_) == 8)
{
lean_object* v_declName_2785_; lean_object* v_type_2786_; lean_object* v_value_2787_; lean_object* v_body_2788_; uint8_t v_nondep_2789_; size_t v___x_2790_; size_t v___x_2791_; uint8_t v___x_2792_; 
v_declName_2785_ = lean_ctor_get(v_e_2747_, 0);
v_type_2786_ = lean_ctor_get(v_e_2747_, 1);
v_value_2787_ = lean_ctor_get(v_e_2747_, 2);
v_body_2788_ = lean_ctor_get(v_e_2747_, 3);
v_nondep_2789_ = lean_ctor_get_uint8(v_e_2747_, sizeof(void*)*4 + 8);
v___x_2790_ = lean_ptr_addr(v_type_2786_);
v___x_2791_ = lean_ptr_addr(v_a_2778_);
v___x_2792_ = lean_usize_dec_eq(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
lean_inc(v_declName_2785_);
lean_dec_ref_known(v_e_2747_, 4);
v___x_2793_ = l_Lean_Expr_letE___override(v_declName_2785_, v_a_2778_, v_a_2780_, v_b_2752_, v_nondep_2789_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2793_);
v___x_2795_ = v___x_2782_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
else
{
size_t v___x_2797_; size_t v___x_2798_; uint8_t v___x_2799_; 
v___x_2797_ = lean_ptr_addr(v_value_2787_);
v___x_2798_ = lean_ptr_addr(v_a_2780_);
v___x_2799_ = lean_usize_dec_eq(v___x_2797_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
lean_inc(v_declName_2785_);
lean_dec_ref_known(v_e_2747_, 4);
v___x_2800_ = l_Lean_Expr_letE___override(v_declName_2785_, v_a_2778_, v_a_2780_, v_b_2752_, v_nondep_2789_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2800_);
v___x_2802_ = v___x_2782_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
else
{
size_t v___x_2804_; size_t v___x_2805_; uint8_t v___x_2806_; 
v___x_2804_ = lean_ptr_addr(v_body_2788_);
v___x_2805_ = lean_ptr_addr(v_b_2752_);
v___x_2806_ = lean_usize_dec_eq(v___x_2804_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
lean_inc(v_declName_2785_);
lean_dec_ref_known(v_e_2747_, 4);
v___x_2807_ = l_Lean_Expr_letE___override(v_declName_2785_, v_a_2778_, v_a_2780_, v_b_2752_, v_nondep_2789_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2807_);
v___x_2809_ = v___x_2782_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
else
{
lean_object* v___x_2812_; 
lean_dec(v_a_2780_);
lean_dec(v_a_2778_);
lean_dec_ref(v_b_2752_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v_e_2747_);
v___x_2812_ = v___x_2782_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_e_2747_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
else
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_dec(v_a_2780_);
lean_dec(v_a_2778_);
lean_dec_ref(v_b_2752_);
lean_dec_ref(v_e_2747_);
v___x_2814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2815_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2814_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2815_);
v___x_2817_ = v___x_2782_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
v___jp_2819_:
{
uint8_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = 0;
v___x_2830_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2823_, v_a_2778_, v_a_2780_, v___y_2828_, v___x_2776_, v___x_2829_, v___y_2821_, v___y_2825_, v___y_2827_, v___y_2820_, v___y_2826_, v___y_2824_, v___y_2822_);
return v___x_2830_;
}
v___jp_2836_:
{
if (v_underBinder_2832_ == 0)
{
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2840_);
goto v___jp_2784_;
}
else
{
if (v_descend_2831_ == 0)
{
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2840_);
goto v___jp_2784_;
}
else
{
lean_del_object(v___x_2782_);
lean_dec_ref(v_b_2752_);
lean_dec_ref(v_e_2747_);
v___y_2820_ = v___y_2837_;
v___y_2821_ = v___y_2838_;
v___y_2822_ = v___y_2839_;
v___y_2823_ = v___y_2840_;
v___y_2824_ = v___y_2841_;
v___y_2825_ = v___y_2842_;
v___y_2826_ = v___y_2844_;
v___y_2827_ = v___y_2843_;
v___y_2828_ = v___y_2845_;
goto v___jp_2819_;
}
}
}
v___jp_2846_:
{
lean_object* v___x_2855_; 
lean_inc(v_a_2780_);
lean_inc(v_a_2778_);
v___x_2855_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2746_, v_n_2749_, v_a_2778_, v_a_2780_, v___y_2848_, v___y_2850_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v_fst_2857_; lean_object* v_snd_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___f_2862_; uint8_t v___x_2863_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v_fst_2857_ = lean_ctor_get(v_a_2856_, 0);
lean_inc_n(v_fst_2857_, 2);
v_snd_2858_ = lean_ctor_get(v_a_2856_, 1);
lean_inc(v_snd_2858_);
lean_dec(v_a_2856_);
v___x_2859_ = lean_box(v___x_2776_);
v___x_2860_ = lean_box(v_isLet_2748_);
v___x_2861_ = lean_box(v_topLevel_2753_);
lean_inc(v_a_2780_);
lean_inc(v_a_2778_);
lean_inc_ref(v_e_2747_);
lean_inc_ref(v_b_2752_);
v___f_2862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2862_, 0, v_fst_2857_);
lean_closure_set(v___f_2862_, 1, v_fvars_2746_);
lean_closure_set(v___f_2862_, 2, v_b_2752_);
lean_closure_set(v___f_2862_, 3, v___x_2859_);
lean_closure_set(v___f_2862_, 4, v_e_2747_);
lean_closure_set(v___f_2862_, 5, v_a_2778_);
lean_closure_set(v___f_2862_, 6, v_a_2780_);
lean_closure_set(v___f_2862_, 7, v___x_2860_);
lean_closure_set(v___f_2862_, 8, v___x_2861_);
v___x_2863_ = lean_unbox(v_fst_2857_);
lean_dec(v_fst_2857_);
if (v___x_2863_ == 0)
{
v___y_2837_ = v___y_2851_;
v___y_2838_ = v___y_2848_;
v___y_2839_ = v___y_2854_;
v___y_2840_ = v_snd_2858_;
v___y_2841_ = v___y_2853_;
v___y_2842_ = v___y_2849_;
v___y_2843_ = v___y_2850_;
v___y_2844_ = v___y_2852_;
v___y_2845_ = v___f_2862_;
goto v___jp_2836_;
}
else
{
if (v___y_2847_ == 0)
{
lean_del_object(v___x_2782_);
lean_dec_ref(v_b_2752_);
lean_dec_ref(v_e_2747_);
v___y_2820_ = v___y_2851_;
v___y_2821_ = v___y_2848_;
v___y_2822_ = v___y_2854_;
v___y_2823_ = v_snd_2858_;
v___y_2824_ = v___y_2853_;
v___y_2825_ = v___y_2849_;
v___y_2826_ = v___y_2852_;
v___y_2827_ = v___y_2850_;
v___y_2828_ = v___f_2862_;
goto v___jp_2819_;
}
else
{
v___y_2837_ = v___y_2851_;
v___y_2838_ = v___y_2848_;
v___y_2839_ = v___y_2854_;
v___y_2840_ = v_snd_2858_;
v___y_2841_ = v___y_2853_;
v___y_2842_ = v___y_2849_;
v___y_2843_ = v___y_2850_;
v___y_2844_ = v___y_2852_;
v___y_2845_ = v___f_2862_;
goto v___jp_2836_;
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_del_object(v___x_2782_);
lean_dec(v_a_2780_);
lean_dec(v_a_2778_);
lean_dec_ref(v_b_2752_);
lean_dec_ref(v_e_2747_);
lean_dec(v_fvars_2746_);
v_a_2864_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2855_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2855_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
v___jp_2872_:
{
if (v_merge_2834_ == 0)
{
v___y_2847_ = v___y_2873_;
v___y_2848_ = v_a_2754_;
v___y_2849_ = v_a_2755_;
v___y_2850_ = v_a_2756_;
v___y_2851_ = v_a_2757_;
v___y_2852_ = v_a_2758_;
v___y_2853_ = v_a_2759_;
v___y_2854_ = v_a_2760_;
goto v___jp_2846_;
}
else
{
lean_object* v___x_2874_; lean_object* v_valueMap_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_st_ref_get(v_a_2756_);
v_valueMap_2875_ = lean_ctor_get(v___x_2874_, 2);
lean_inc_ref(v_valueMap_2875_);
lean_dec(v___x_2874_);
v___x_2876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2875_, v_a_2780_);
lean_dec_ref(v_valueMap_2875_);
if (lean_obj_tag(v___x_2876_) == 1)
{
lean_del_object(v___x_2782_);
lean_dec(v_a_2780_);
lean_dec(v_a_2778_);
lean_dec(v_n_2749_);
lean_dec_ref(v_e_2747_);
if (v_isLet_2748_ == 0)
{
lean_object* v_val_2877_; 
v_val_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___y_2763_ = v_val_2877_;
v___y_2764_ = v_a_2754_;
v___y_2765_ = v_a_2755_;
v___y_2766_ = v_a_2756_;
v___y_2767_ = v_a_2757_;
v___y_2768_ = v_a_2758_;
v___y_2769_ = v_a_2759_;
v___y_2770_ = v_a_2760_;
goto v___jp_2762_;
}
else
{
if (v_lift_2835_ == 0)
{
lean_object* v_val_2878_; 
v_val_2878_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v___x_2876_, 1);
v___y_2763_ = v_val_2878_;
v___y_2764_ = v_a_2754_;
v___y_2765_ = v_a_2755_;
v___y_2766_ = v_a_2756_;
v___y_2767_ = v_a_2757_;
v___y_2768_ = v_a_2758_;
v___y_2769_ = v_a_2759_;
v___y_2770_ = v_a_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v_val_2879_; lean_object* v___x_2880_; 
v_val_2879_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2880_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2879_, v_a_2756_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_dec_ref_known(v___x_2880_, 1);
v___y_2763_ = v_val_2879_;
v___y_2764_ = v_a_2754_;
v___y_2765_ = v_a_2755_;
v___y_2766_ = v_a_2756_;
v___y_2767_ = v_a_2757_;
v___y_2768_ = v_a_2758_;
v___y_2769_ = v_a_2759_;
v___y_2770_ = v_a_2760_;
goto v___jp_2762_;
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_val_2879_);
lean_dec_ref(v_b_2752_);
lean_dec(v_fvars_2746_);
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2880_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2876_);
v___y_2847_ = v___y_2873_;
v___y_2848_ = v_a_2754_;
v___y_2849_ = v_a_2755_;
v___y_2850_ = v_a_2756_;
v___y_2851_ = v_a_2757_;
v___y_2852_ = v_a_2758_;
v___y_2853_ = v_a_2759_;
v___y_2854_ = v_a_2760_;
goto v___jp_2846_;
}
}
}
}
}
else
{
lean_dec(v_a_2778_);
lean_dec_ref(v_b_2752_);
lean_dec(v_n_2749_);
lean_dec_ref(v_e_2747_);
lean_dec(v_fvars_2746_);
return v___x_2779_;
}
}
else
{
lean_dec_ref(v_b_2752_);
lean_dec_ref(v_v_2751_);
lean_dec(v_n_2749_);
lean_dec_ref(v_e_2747_);
lean_dec(v_fvars_2746_);
return v___x_2777_;
}
v___jp_2762_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_inc(v___y_2763_);
v___x_2771_ = l_Lean_Expr_fvar___override(v___y_2763_);
v___x_2772_ = lean_expr_instantiate1(v_b_2752_, v___x_2771_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v_b_2752_);
v___x_2773_ = lean_box(v_topLevel_2753_);
v___x_2774_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2774_, 0, v_fvars_2746_);
lean_closure_set(v___x_2774_, 1, v___x_2772_);
lean_closure_set(v___x_2774_, 2, v___x_2773_);
v___x_2775_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2763_, v___x_2774_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2763_);
return v___x_2775_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2746_ = stack[0].m_obj;
lean_object* v_e_2747_ = stack[1].m_obj;
uint8_t v_isLet_2748_ = stack[2].m_num;
lean_object* v_n_2749_ = stack[3].m_obj;
lean_object* v_t_2750_ = stack[4].m_obj;
lean_object* v_v_2751_ = stack[5].m_obj;
lean_object* v_b_2752_ = stack[6].m_obj;
uint8_t v_topLevel_2753_ = stack[7].m_num;
lean_object* v_a_2754_ = stack[8].m_obj;
lean_object* v_a_2755_ = stack[9].m_obj;
lean_object* v_a_2756_ = stack[10].m_obj;
lean_object* v_a_2757_ = stack[11].m_obj;
lean_object* v_a_2758_ = stack[12].m_obj;
lean_object* v_a_2759_ = stack[13].m_obj;
lean_object* v_a_2760_ = stack[14].m_obj;
lean_object* v_res_2892_;
v_res_2892_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2746_, v_e_2747_, v_isLet_2748_, v_n_2749_, v_t_2750_, v_v_2751_, v_b_2752_, v_topLevel_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
stack->m_obj
 = v_res_2892_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2893_, lean_object* v_struct_2894_, lean_object* v___y_2895_, lean_object* v_typeName_2896_, lean_object* v_idx_2897_, lean_object* v_e_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
uint8_t v___y_42347__boxed_2907_; lean_object* v_res_2908_; 
v___y_42347__boxed_2907_ = lean_unbox(v___y_2895_);
v_res_2908_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2893_, v_struct_2894_, v___y_42347__boxed_2907_, v_typeName_2896_, v_idx_2897_, v_e_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2908_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2912_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2913_ = lean_unsigned_to_nat(75u);
v___x_2914_ = lean_unsigned_to_nat(229u);
v___x_2915_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2916_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2917_ = l_mkPanicMessageWithDecl(v___x_2916_, v___x_2915_, v___x_2914_, v___x_2913_, v___x_2912_);
return v___x_2917_;
}
}
lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2918_, lean_object* v_e_2919_, lean_object* v_fvars_2920_, uint8_t v___x_2921_, uint8_t v_topLevel_2922_, uint8_t v___y_2923_, lean_object* v_____r_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_k_2934_; 
switch(lean_obj_tag(v_e_2919_))
{
case 5:
{
lean_object* v___x_2937_; lean_object* v_dummy_2938_; lean_object* v_nargs_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2937_ = l_Lean_Expr_getAppFn(v_e_2919_);
v_dummy_2938_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2939_ = l_Lean_Expr_getAppNumArgs(v_e_2919_);
lean_inc(v_nargs_2939_);
v___x_2940_ = lean_mk_array(v_nargs_2939_, v_dummy_2938_);
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_nat_sub(v_nargs_2939_, v___x_2941_);
lean_dec(v_nargs_2939_);
lean_inc_ref(v_e_2919_);
v___x_2943_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2919_, v___x_2940_, v___x_2942_);
v___x_2944_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2944_, 0, v_fvars_2920_);
lean_closure_set(v___x_2944_, 1, v___x_2937_);
lean_closure_set(v___x_2944_, 2, v___x_2943_);
v_k_2934_ = v___x_2944_;
goto v___jp_2933_;
}
case 6:
{
lean_object* v_binderName_2945_; lean_object* v_binderType_2946_; lean_object* v_body_2947_; uint8_t v_binderInfo_2948_; lean_object* v___x_2949_; lean_object* v___f_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_binderName_2945_ = lean_ctor_get(v_e_2919_, 0);
v_binderType_2946_ = lean_ctor_get(v_e_2919_, 1);
v_body_2947_ = lean_ctor_get(v_e_2919_, 2);
v_binderInfo_2948_ = lean_ctor_get_uint8(v_e_2919_, sizeof(void*)*3 + 8);
v___x_2949_ = lean_box(v_binderInfo_2948_);
lean_inc_ref(v_e_2919_);
lean_inc_ref_n(v_body_2947_, 2);
lean_inc_n(v_binderName_2945_, 2);
lean_inc_ref_n(v_binderType_2946_, 2);
v___f_2950_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2950_, 0, v_binderType_2946_);
lean_closure_set(v___f_2950_, 1, v_binderName_2945_);
lean_closure_set(v___f_2950_, 2, v___x_2949_);
lean_closure_set(v___f_2950_, 3, v_body_2947_);
lean_closure_set(v___f_2950_, 4, v_e_2919_);
v___x_2951_ = lean_box(v_binderInfo_2948_);
v___x_2952_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2952_, 0, v_fvars_2920_);
lean_closure_set(v___x_2952_, 1, v_binderName_2945_);
lean_closure_set(v___x_2952_, 2, v_binderType_2946_);
lean_closure_set(v___x_2952_, 3, v_body_2947_);
lean_closure_set(v___x_2952_, 4, v___x_2951_);
lean_closure_set(v___x_2952_, 5, v___f_2950_);
v_k_2934_ = v___x_2952_;
goto v___jp_2933_;
}
case 7:
{
lean_object* v_binderName_2953_; lean_object* v_binderType_2954_; lean_object* v_body_2955_; uint8_t v_binderInfo_2956_; lean_object* v___x_2957_; lean_object* v___f_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_binderName_2953_ = lean_ctor_get(v_e_2919_, 0);
v_binderType_2954_ = lean_ctor_get(v_e_2919_, 1);
v_body_2955_ = lean_ctor_get(v_e_2919_, 2);
v_binderInfo_2956_ = lean_ctor_get_uint8(v_e_2919_, sizeof(void*)*3 + 8);
v___x_2957_ = lean_box(v_binderInfo_2956_);
lean_inc_ref(v_e_2919_);
lean_inc_ref_n(v_body_2955_, 2);
lean_inc_n(v_binderName_2953_, 2);
lean_inc_ref_n(v_binderType_2954_, 2);
v___f_2958_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2958_, 0, v_binderType_2954_);
lean_closure_set(v___f_2958_, 1, v_binderName_2953_);
lean_closure_set(v___f_2958_, 2, v___x_2957_);
lean_closure_set(v___f_2958_, 3, v_body_2955_);
lean_closure_set(v___f_2958_, 4, v_e_2919_);
v___x_2959_ = lean_box(v_binderInfo_2956_);
v___x_2960_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2960_, 0, v_fvars_2920_);
lean_closure_set(v___x_2960_, 1, v_binderName_2953_);
lean_closure_set(v___x_2960_, 2, v_binderType_2954_);
lean_closure_set(v___x_2960_, 3, v_body_2955_);
lean_closure_set(v___x_2960_, 4, v___x_2959_);
lean_closure_set(v___x_2960_, 5, v___f_2958_);
v_k_2934_ = v___x_2960_;
goto v___jp_2933_;
}
case 8:
{
uint8_t v_nondep_2961_; 
v_nondep_2961_ = lean_ctor_get_uint8(v_e_2919_, sizeof(void*)*4 + 8);
if (v_nondep_2961_ == 0)
{
lean_object* v_declName_2962_; lean_object* v_type_2963_; lean_object* v_value_2964_; lean_object* v_body_2965_; lean_object* v___x_2966_; 
v_declName_2962_ = lean_ctor_get(v_e_2919_, 0);
lean_inc(v_declName_2962_);
v_type_2963_ = lean_ctor_get(v_e_2919_, 1);
lean_inc_ref(v_type_2963_);
v_value_2964_ = lean_ctor_get(v_e_2919_, 2);
lean_inc_ref(v_value_2964_);
v_body_2965_ = lean_ctor_get(v_e_2919_, 3);
lean_inc_ref(v_body_2965_);
v___x_2966_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2920_, v_e_2919_, v___x_2921_, v_declName_2962_, v_type_2963_, v_value_2964_, v_body_2965_, v_topLevel_2922_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2966_;
}
else
{
lean_object* v_declName_2967_; lean_object* v_type_2968_; lean_object* v_value_2969_; lean_object* v_body_2970_; lean_object* v___x_2971_; 
v_declName_2967_ = lean_ctor_get(v_e_2919_, 0);
lean_inc(v_declName_2967_);
v_type_2968_ = lean_ctor_get(v_e_2919_, 1);
lean_inc_ref(v_type_2968_);
v_value_2969_ = lean_ctor_get(v_e_2919_, 2);
lean_inc_ref(v_value_2969_);
v_body_2970_ = lean_ctor_get(v_e_2919_, 3);
lean_inc_ref(v_body_2970_);
v___x_2971_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2920_, v_e_2919_, v___y_2923_, v_declName_2967_, v_type_2968_, v_value_2969_, v_body_2970_, v_topLevel_2922_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2971_;
}
}
case 10:
{
lean_object* v_data_2972_; lean_object* v_expr_2973_; lean_object* v___x_2974_; 
v_data_2972_ = lean_ctor_get(v_e_2919_, 0);
v_expr_2973_ = lean_ctor_get(v_e_2919_, 1);
lean_inc_ref(v_expr_2973_);
v___x_2974_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2920_, v_expr_2973_, v_topLevel_2922_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2989_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2989_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2989_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
size_t v___x_2979_; size_t v___x_2980_; uint8_t v___x_2981_; 
v___x_2979_ = lean_ptr_addr(v_expr_2973_);
v___x_2980_ = lean_ptr_addr(v_a_2975_);
v___x_2981_ = lean_usize_dec_eq(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
lean_inc(v_data_2972_);
lean_dec_ref_known(v_e_2919_, 2);
v___x_2982_ = l_Lean_Expr_mdata___override(v_data_2972_, v_a_2975_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2982_);
v___x_2984_ = v___x_2977_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
else
{
lean_object* v___x_2987_; 
lean_dec(v_a_2975_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v_e_2919_);
v___x_2987_ = v___x_2977_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_e_2919_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2919_, 2);
return v___x_2974_;
}
}
case 11:
{
lean_object* v_typeName_2990_; lean_object* v_idx_2991_; lean_object* v_struct_2992_; lean_object* v___x_2993_; lean_object* v___f_2994_; 
v_typeName_2990_ = lean_ctor_get(v_e_2919_, 0);
v_idx_2991_ = lean_ctor_get(v_e_2919_, 1);
v_struct_2992_ = lean_ctor_get(v_e_2919_, 2);
v___x_2993_ = lean_box(v___y_2923_);
lean_inc_ref(v_e_2919_);
lean_inc(v_idx_2991_);
lean_inc(v_typeName_2990_);
lean_inc_ref(v_struct_2992_);
v___f_2994_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2994_, 0, v_fvars_2920_);
lean_closure_set(v___f_2994_, 1, v_struct_2992_);
lean_closure_set(v___f_2994_, 2, v___x_2993_);
lean_closure_set(v___f_2994_, 3, v_typeName_2990_);
lean_closure_set(v___f_2994_, 4, v_idx_2991_);
lean_closure_set(v___f_2994_, 5, v_e_2919_);
v_k_2934_ = v___f_2994_;
goto v___jp_2933_;
}
default: 
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec(v_fvars_2920_);
lean_dec_ref(v_e_2919_);
v___x_2995_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2996_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2995_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2996_;
}
}
v___jp_2933_:
{
if (v_descend_2918_ == 0)
{
lean_object* v___x_2935_; 
lean_dec_ref(v_k_2934_);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_e_2919_);
return v___x_2935_;
}
else
{
lean_object* v___x_2936_; 
lean_dec_ref(v_e_2919_);
lean_inc(v___y_2931_);
lean_inc_ref(v___y_2930_);
lean_inc(v___y_2929_);
lean_inc_ref(v___y_2928_);
lean_inc(v___y_2927_);
lean_inc(v___y_2926_);
lean_inc_ref(v___y_2925_);
v___x_2936_ = lean_apply_8(v_k_2934_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, lean_box(0));
return v___x_2936_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractCore___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_descend_2918_ = stack[0].m_num;
lean_object* v_e_2919_ = stack[1].m_obj;
lean_object* v_fvars_2920_ = stack[2].m_obj;
uint8_t v___x_2921_ = stack[3].m_num;
uint8_t v_topLevel_2922_ = stack[4].m_num;
uint8_t v___y_2923_ = stack[5].m_num;
lean_object* v_____r_2924_ = stack[6].m_obj;
lean_object* v___y_2925_ = stack[7].m_obj;
lean_object* v___y_2926_ = stack[8].m_obj;
lean_object* v___y_2927_ = stack[9].m_obj;
lean_object* v___y_2928_ = stack[10].m_obj;
lean_object* v___y_2929_ = stack[11].m_obj;
lean_object* v___y_2930_ = stack[12].m_obj;
lean_object* v___y_2931_ = stack[13].m_obj;
lean_object* v_res_2997_;
v_res_2997_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_2918_, v_e_2919_, v_fvars_2920_, v___x_2921_, v_topLevel_2922_, v___y_2923_, v_____r_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
stack->m_obj
 = v_res_2997_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2998_, lean_object* v_e_2999_, lean_object* v_fvars_3000_, lean_object* v___x_3001_, lean_object* v_topLevel_3002_, lean_object* v___y_3003_, lean_object* v_____r_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
uint8_t v_descend_boxed_3013_; uint8_t v___x_42500__boxed_3014_; uint8_t v_topLevel_boxed_3015_; uint8_t v___y_42501__boxed_3016_; lean_object* v_res_3017_; 
v_descend_boxed_3013_ = lean_unbox(v_descend_2998_);
v___x_42500__boxed_3014_ = lean_unbox(v___x_3001_);
v_topLevel_boxed_3015_ = lean_unbox(v_topLevel_3002_);
v___y_42501__boxed_3016_ = lean_unbox(v___y_3003_);
v_res_3017_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_3013_, v_e_2999_, v_fvars_3000_, v___x_42500__boxed_3014_, v_topLevel_boxed_3015_, v___y_42501__boxed_3016_, v_____r_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3017_;
}
}
lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_3018_, lean_object* v_e_3019_, uint8_t v_topLevel_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___y_3030_; lean_object* v_a_3031_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3041_; lean_object* v___y_3042_; uint8_t v___x_3045_; 
v___x_3045_ = l_Lean_Expr_isAtomic(v_e_3019_);
if (v___x_3045_ == 0)
{
uint8_t v_proofs_3046_; uint8_t v_types_3047_; uint8_t v_descend_3048_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; uint8_t v___y_3053_; uint8_t v___y_3070_; 
v_proofs_3046_ = lean_ctor_get_uint8(v_a_3021_, 0);
v_types_3047_ = lean_ctor_get_uint8(v_a_3021_, 1);
v_descend_3048_ = lean_ctor_get_uint8(v_a_3021_, 3);
if (v_descend_3048_ == 0)
{
goto v___jp_3094_;
}
else
{
if (v___x_3045_ == 0)
{
v___y_3070_ = v___x_3045_;
goto v___jp_3069_;
}
else
{
goto v___jp_3094_;
}
}
v___jp_3049_:
{
if (v___y_3053_ == 0)
{
lean_dec_ref(v___y_3051_);
if (v_proofs_3046_ == 0)
{
lean_object* v___x_3054_; 
lean_inc_ref(v_e_3019_);
v___x_3054_ = l_Lean_Meta_isProof(v_e_3019_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; uint8_t v___x_3056_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3054_, 1);
v___x_3056_ = lean_unbox(v_a_3055_);
lean_dec(v_a_3055_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v_e_3019_);
v___x_3057_ = lean_box(0);
lean_inc(v_a_3027_);
lean_inc_ref(v_a_3026_);
lean_inc(v_a_3025_);
lean_inc_ref(v_a_3024_);
lean_inc(v_a_3023_);
lean_inc(v_a_3022_);
lean_inc_ref(v_a_3021_);
v___x_3058_ = lean_apply_9(v___y_3050_, v___x_3057_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, lean_box(0));
v___y_3037_ = v___y_3052_;
v___y_3038_ = v___x_3058_;
goto v___jp_3036_;
}
else
{
lean_dec_ref(v___y_3050_);
v___y_3030_ = v___y_3052_;
v_a_3031_ = v_e_3019_;
goto v___jp_3029_;
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v___y_3052_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v_e_3019_);
v_a_3059_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3054_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3054_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec_ref(v_e_3019_);
v___x_3067_ = lean_box(0);
lean_inc(v_a_3027_);
lean_inc_ref(v_a_3026_);
lean_inc(v_a_3025_);
lean_inc_ref(v_a_3024_);
lean_inc(v_a_3023_);
lean_inc(v_a_3022_);
lean_inc_ref(v_a_3021_);
v___x_3068_ = lean_apply_9(v___y_3050_, v___x_3067_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, lean_box(0));
v___y_3037_ = v___y_3052_;
v___y_3038_ = v___x_3068_;
goto v___jp_3036_;
}
}
else
{
lean_dec_ref(v___y_3050_);
lean_dec_ref(v_e_3019_);
v___y_3041_ = v___y_3051_;
v___y_3042_ = v___y_3052_;
goto v___jp_3040_;
}
}
v___jp_3069_:
{
if (v___y_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = lean_box(v_topLevel_3020_);
lean_inc_ref(v_e_3019_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v_e_3019_);
v___x_3073_ = lean_st_ref_get(v_a_3022_);
v___x_3074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3073_, v___x_3072_);
lean_dec(v___x_3073_);
if (lean_obj_tag(v___x_3074_) == 0)
{
uint8_t v___x_3075_; 
v___x_3075_ = l_Lean_Meta_ExtractLets_containsLet(v_e_3019_);
if (v___x_3075_ == 0)
{
lean_dec(v_fvars_3018_);
v___y_3030_ = v___x_3072_;
v_a_3031_ = v_e_3019_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___f_3082_; 
v___x_3076_ = lean_box(v_descend_3048_);
v___x_3077_ = lean_box(v___x_3075_);
v___x_3078_ = lean_box(v_topLevel_3020_);
v___x_3079_ = lean_box(v___y_3070_);
lean_inc_ref_n(v_e_3019_, 2);
v___f_3080_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3080_, 0, v___x_3076_);
lean_closure_set(v___f_3080_, 1, v_e_3019_);
lean_closure_set(v___f_3080_, 2, v_fvars_3018_);
lean_closure_set(v___f_3080_, 3, v___x_3077_);
lean_closure_set(v___f_3080_, 4, v___x_3078_);
lean_closure_set(v___f_3080_, 5, v___x_3079_);
v___x_3081_ = lean_box(v_types_3047_);
lean_inc_ref(v___f_3080_);
v___f_3082_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3082_, 0, v___x_3081_);
lean_closure_set(v___f_3082_, 1, v_e_3019_);
lean_closure_set(v___f_3082_, 2, v___f_3080_);
if (v_topLevel_3020_ == 0)
{
v___y_3050_ = v___f_3082_;
v___y_3051_ = v___f_3080_;
v___y_3052_ = v___x_3072_;
v___y_3053_ = v___x_3045_;
goto v___jp_3049_;
}
else
{
uint8_t v___x_3083_; 
v___x_3083_ = l_Lean_Expr_isLet(v_e_3019_);
if (v___x_3083_ == 0)
{
uint8_t v___x_3084_; 
v___x_3084_ = l_Lean_Expr_isMData(v_e_3019_);
v___y_3050_ = v___f_3082_;
v___y_3051_ = v___f_3080_;
v___y_3052_ = v___x_3072_;
v___y_3053_ = v___x_3084_;
goto v___jp_3049_;
}
else
{
lean_dec_ref(v___f_3082_);
lean_dec_ref(v_e_3019_);
v___y_3041_ = v___f_3080_;
v___y_3042_ = v___x_3072_;
goto v___jp_3040_;
}
}
}
}
else
{
lean_object* v_val_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref_known(v___x_3072_, 2);
lean_dec_ref(v_e_3019_);
lean_dec(v_fvars_3018_);
v_val_3085_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3074_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_val_3085_);
lean_dec(v___x_3074_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 0);
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_val_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v___x_3093_; 
lean_dec(v_fvars_3018_);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_e_3019_);
return v___x_3093_;
}
}
v___jp_3094_:
{
if (v_topLevel_3020_ == 0)
{
lean_object* v___x_3095_; 
lean_dec(v_fvars_3018_);
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_e_3019_);
return v___x_3095_;
}
else
{
v___y_3070_ = v___x_3045_;
goto v___jp_3069_;
}
}
}
else
{
lean_object* v___x_3096_; 
lean_dec(v_fvars_3018_);
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v_e_3019_);
return v___x_3096_;
}
v___jp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3032_ = lean_st_ref_take(v_a_3022_);
lean_inc_ref(v_a_3031_);
v___x_3033_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3032_, v___y_3030_, v_a_3031_);
v___x_3034_ = lean_st_ref_put(v_a_3022_, v___x_3033_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_a_3031_);
return v___x_3035_;
}
v___jp_3036_:
{
if (lean_obj_tag(v___y_3038_) == 0)
{
lean_object* v_a_3039_; 
v_a_3039_ = lean_ctor_get(v___y_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___y_3038_, 1);
v___y_3030_ = v___y_3037_;
v_a_3031_ = v_a_3039_;
goto v___jp_3029_;
}
else
{
lean_dec_ref(v___y_3037_);
return v___y_3038_;
}
}
v___jp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_box(0);
lean_inc(v_a_3027_);
lean_inc_ref(v_a_3026_);
lean_inc(v_a_3025_);
lean_inc_ref(v_a_3024_);
lean_inc(v_a_3023_);
lean_inc(v_a_3022_);
lean_inc_ref(v_a_3021_);
v___x_3044_ = lean_apply_9(v___y_3041_, v___x_3043_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, lean_box(0));
v___y_3037_ = v___y_3042_;
v___y_3038_ = v___x_3044_;
goto v___jp_3036_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3018_ = stack[0].m_obj;
lean_object* v_e_3019_ = stack[1].m_obj;
uint8_t v_topLevel_3020_ = stack[2].m_num;
lean_object* v_a_3021_ = stack[3].m_obj;
lean_object* v_a_3022_ = stack[4].m_obj;
lean_object* v_a_3023_ = stack[5].m_obj;
lean_object* v_a_3024_ = stack[6].m_obj;
lean_object* v_a_3025_ = stack[7].m_obj;
lean_object* v_a_3026_ = stack[8].m_obj;
lean_object* v_a_3027_ = stack[9].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3018_, v_e_3019_, v_topLevel_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
stack->m_obj
 = v_res_3097_;
}
lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3098_, lean_object* v_struct_3099_, uint8_t v___y_3100_, lean_object* v_typeName_3101_, lean_object* v_idx_3102_, lean_object* v_e_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v___x_3112_; 
lean_inc_ref(v_struct_3099_);
v___x_3112_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3098_, v_struct_3099_, v___y_3100_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3127_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3127_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3127_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
size_t v___x_3117_; size_t v___x_3118_; uint8_t v___x_3119_; 
v___x_3117_ = lean_ptr_addr(v_struct_3099_);
lean_dec_ref(v_struct_3099_);
v___x_3118_ = lean_ptr_addr(v_a_3113_);
v___x_3119_ = lean_usize_dec_eq(v___x_3117_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_dec_ref(v_e_3103_);
v___x_3120_ = l_Lean_Expr_proj___override(v_typeName_3101_, v_idx_3102_, v_a_3113_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3120_);
v___x_3122_ = v___x_3115_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
else
{
lean_object* v___x_3125_; 
lean_dec(v_a_3113_);
lean_dec(v_idx_3102_);
lean_dec(v_typeName_3101_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_e_3103_);
v___x_3125_ = v___x_3115_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_e_3103_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_dec_ref(v_e_3103_);
lean_dec(v_idx_3102_);
lean_dec(v_typeName_3101_);
lean_dec_ref(v_struct_3099_);
return v___x_3112_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractCore___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3098_ = stack[0].m_obj;
lean_object* v_struct_3099_ = stack[1].m_obj;
uint8_t v___y_3100_ = stack[2].m_num;
lean_object* v_typeName_3101_ = stack[3].m_obj;
lean_object* v_idx_3102_ = stack[4].m_obj;
lean_object* v_e_3103_ = stack[5].m_obj;
lean_object* v___y_3104_ = stack[6].m_obj;
lean_object* v___y_3105_ = stack[7].m_obj;
lean_object* v___y_3106_ = stack[8].m_obj;
lean_object* v___y_3107_ = stack[9].m_obj;
lean_object* v___y_3108_ = stack[10].m_obj;
lean_object* v___y_3109_ = stack[11].m_obj;
lean_object* v___y_3110_ = stack[12].m_obj;
lean_object* v_res_3128_;
v_res_3128_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_3098_, v_struct_3099_, v___y_3100_, v_typeName_3101_, v_idx_3102_, v_e_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
stack->m_obj
 = v_res_3128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3129_, lean_object* v_sz_3130_, lean_object* v_i_3131_, lean_object* v_bs_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
size_t v_sz_boxed_3141_; size_t v_i_boxed_3142_; lean_object* v_res_3143_; 
v_sz_boxed_3141_ = lean_unbox_usize(v_sz_3130_);
lean_dec(v_sz_3130_);
v_i_boxed_3142_ = lean_unbox_usize(v_i_3131_);
lean_dec(v_i_3131_);
v_res_3143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3129_, v_sz_boxed_3141_, v_i_boxed_3142_, v_bs_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3144_, lean_object* v_fst_3145_, lean_object* v_fvars_3146_, lean_object* v_a_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3144_, v_fst_3145_, v_fvars_3146_, v_a_3147_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec_ref(v_fst_3145_);
lean_dec(v_upperBound_3144_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3158_, lean_object* v_e_3159_, lean_object* v_isLet_3160_, lean_object* v_n_3161_, lean_object* v_t_3162_, lean_object* v_v_3163_, lean_object* v_b_3164_, lean_object* v_topLevel_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_){
_start:
{
uint8_t v_isLet_boxed_3174_; uint8_t v_topLevel_boxed_3175_; lean_object* v_res_3176_; 
v_isLet_boxed_3174_ = lean_unbox(v_isLet_3160_);
v_topLevel_boxed_3175_ = lean_unbox(v_topLevel_3165_);
v_res_3176_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3158_, v_e_3159_, v_isLet_boxed_3174_, v_n_3161_, v_t_3162_, v_v_3163_, v_b_3164_, v_topLevel_boxed_3175_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
return v_res_3176_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3177_, lean_object* v_name_3178_, lean_object* v_type_3179_, lean_object* v_val_3180_, lean_object* v_k_3181_, uint8_t v_nondep_3182_, uint8_t v_kind_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3178_, v_type_3179_, v_val_3180_, v_k_3181_, v_nondep_3182_, v_kind_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3178_ = stack[1].m_obj;
lean_object* v_type_3179_ = stack[2].m_obj;
lean_object* v_val_3180_ = stack[3].m_obj;
lean_object* v_k_3181_ = stack[4].m_obj;
uint8_t v_nondep_3182_ = stack[5].m_num;
uint8_t v_kind_3183_ = stack[6].m_num;
lean_object* v___y_3184_ = stack[7].m_obj;
lean_object* v___y_3185_ = stack[8].m_obj;
lean_object* v___y_3186_ = stack[9].m_obj;
lean_object* v___y_3187_ = stack[10].m_obj;
lean_object* v___y_3188_ = stack[11].m_obj;
lean_object* v___y_3189_ = stack[12].m_obj;
lean_object* v___y_3190_ = stack[13].m_obj;
lean_object* v_res_3193_;
v_res_3193_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_box(0), v_name_3178_, v_type_3179_, v_val_3180_, v_k_3181_, v_nondep_3182_, v_kind_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
stack->m_obj
 = v_res_3193_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3194_, lean_object* v_name_3195_, lean_object* v_type_3196_, lean_object* v_val_3197_, lean_object* v_k_3198_, lean_object* v_nondep_3199_, lean_object* v_kind_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v_nondep_boxed_3209_; uint8_t v_kind_boxed_3210_; lean_object* v_res_3211_; 
v_nondep_boxed_3209_ = lean_unbox(v_nondep_3199_);
v_kind_boxed_3210_ = lean_unbox(v_kind_3200_);
v_res_3211_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3194_, v_name_3195_, v_type_3196_, v_val_3197_, v_k_3198_, v_nondep_boxed_3209_, v_kind_boxed_3210_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3212_, lean_object* v_m_3213_, lean_object* v_a_3214_, lean_object* v_b_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3213_, v_a_3214_, v_b_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3217_, lean_object* v_m_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3218_, v_a_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3221_, lean_object* v_m_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3221_, v_m_3222_, v_a_3223_);
lean_dec_ref(v_a_3223_);
lean_dec_ref(v_m_3222_);
return v_res_3224_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3225_, lean_object* v_fst_3226_, lean_object* v_fvars_3227_, lean_object* v_inst_3228_, lean_object* v_R_3229_, lean_object* v_a_3230_, lean_object* v_b_3231_, lean_object* v_c_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3225_, v_fst_3226_, v_fvars_3227_, v_a_3230_, v_b_3231_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3225_ = stack[0].m_obj;
lean_object* v_fst_3226_ = stack[1].m_obj;
lean_object* v_fvars_3227_ = stack[2].m_obj;
lean_object* v_a_3230_ = stack[5].m_obj;
lean_object* v_b_3231_ = stack[6].m_obj;
lean_object* v___y_3233_ = stack[8].m_obj;
lean_object* v___y_3234_ = stack[9].m_obj;
lean_object* v___y_3235_ = stack[10].m_obj;
lean_object* v___y_3236_ = stack[11].m_obj;
lean_object* v___y_3237_ = stack[12].m_obj;
lean_object* v___y_3238_ = stack[13].m_obj;
lean_object* v___y_3239_ = stack[14].m_obj;
lean_object* v_res_3242_;
v_res_3242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3225_, v_fst_3226_, v_fvars_3227_, lean_box(0), lean_box(0), v_a_3230_, v_b_3231_, lean_box(0), v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
stack->m_obj
 = v_res_3242_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3243_, lean_object* v_fst_3244_, lean_object* v_fvars_3245_, lean_object* v_inst_3246_, lean_object* v_R_3247_, lean_object* v_a_3248_, lean_object* v_b_3249_, lean_object* v_c_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3243_, v_fst_3244_, v_fvars_3245_, v_inst_3246_, v_R_3247_, v_a_3248_, v_b_3249_, v_c_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v_fst_3244_);
lean_dec(v_upperBound_3243_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3260_, lean_object* v_m_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3261_, v_a_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3264_, lean_object* v_m_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3264_, v_m_3265_, v_a_3266_);
lean_dec_ref(v_a_3266_);
lean_dec_ref(v_m_3265_);
return v_res_3267_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3268_, lean_object* v_a_3269_, lean_object* v_x_3270_){
_start:
{
uint8_t v___x_3271_; 
v___x_3271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3269_, v_x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3269_ = stack[1].m_obj;
lean_object* v_x_3270_ = stack[2].m_obj;
uint8_t v_res_3272_;
v_res_3272_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_box(0), v_a_3269_, v_x_3270_);
stack->m_num = v_res_3272_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3273_, lean_object* v_a_3274_, lean_object* v_x_3275_){
_start:
{
uint8_t v_res_3276_; lean_object* v_r_3277_; 
v_res_3276_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3273_, v_a_3274_, v_x_3275_);
lean_dec(v_x_3275_);
lean_dec_ref(v_a_3274_);
v_r_3277_ = lean_box(v_res_3276_);
return v_r_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3278_, lean_object* v_data_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3281_, lean_object* v_a_3282_, lean_object* v_b_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3282_, v_b_3283_, v_x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3286_, lean_object* v_a_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3287_, v_x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3290_, lean_object* v_a_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3290_, v_a_3291_, v_x_3292_);
lean_dec(v_x_3292_);
lean_dec_ref(v_a_3291_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3294_, lean_object* v_a_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3295_, v_x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3298_, lean_object* v_a_3299_, lean_object* v_x_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3298_, v_a_3299_, v_x_3300_);
lean_dec(v_x_3300_);
lean_dec_ref(v_a_3299_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3302_, lean_object* v_i_3303_, lean_object* v_source_3304_, lean_object* v_target_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3303_, v_source_3304_, v_target_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3308_, v_x_3309_);
return v___x_3310_;
}
}
lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___x_3320_; lean_object* v_a_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3320_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3311_, v_a_3316_);
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = lean_box(0);
v___x_3323_ = 1;
v___x_3324_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3322_, v_a_3321_, v___x_3323_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
return v___x_3324_;
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extractTopLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3311_ = stack[0].m_obj;
lean_object* v_a_3312_ = stack[1].m_obj;
lean_object* v_a_3313_ = stack[2].m_obj;
lean_object* v_a_3314_ = stack[3].m_obj;
lean_object* v_a_3315_ = stack[4].m_obj;
lean_object* v_a_3316_ = stack[5].m_obj;
lean_object* v_a_3317_ = stack[6].m_obj;
lean_object* v_a_3318_ = stack[7].m_obj;
lean_object* v_res_3325_;
v_res_3325_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
stack->m_obj
 = v_res_3325_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec(v_a_3328_);
lean_dec_ref(v_a_3327_);
return v_res_3335_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3336_, size_t v_i_3337_, lean_object* v_bs_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v___x_3347_; 
v___x_3347_ = lean_usize_dec_lt(v_i_3337_, v_sz_3336_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v_bs_3338_);
return v___x_3348_;
}
else
{
lean_object* v_v_3349_; lean_object* v___x_3350_; lean_object* v_bs_x27_3351_; lean_object* v___x_3352_; 
v_v_3349_ = lean_array_uget(v_bs_3338_, v_i_3337_);
v___x_3350_ = lean_unsigned_to_nat(0u);
v_bs_x27_3351_ = lean_array_uset(v_bs_3338_, v_i_3337_, v___x_3350_);
v___x_3352_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3349_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; size_t v___x_3354_; size_t v___x_3355_; lean_object* v___x_3356_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3352_, 1);
v___x_3354_ = ((size_t)1ULL);
v___x_3355_ = lean_usize_add(v_i_3337_, v___x_3354_);
v___x_3356_ = lean_array_uset(v_bs_x27_3351_, v_i_3337_, v_a_3353_);
v_i_3337_ = v___x_3355_;
v_bs_3338_ = v___x_3356_;
goto _start;
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec_ref(v_bs_x27_3351_);
v_a_3358_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3352_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3352_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3336_ = stack[0].m_num;
size_t v_i_3337_ = stack[1].m_num;
lean_object* v_bs_3338_ = stack[2].m_obj;
lean_object* v___y_3339_ = stack[3].m_obj;
lean_object* v___y_3340_ = stack[4].m_obj;
lean_object* v___y_3341_ = stack[5].m_obj;
lean_object* v___y_3342_ = stack[6].m_obj;
lean_object* v___y_3343_ = stack[7].m_obj;
lean_object* v___y_3344_ = stack[8].m_obj;
lean_object* v___y_3345_ = stack[9].m_obj;
lean_object* v_res_3366_;
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3336_, v_i_3337_, v_bs_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
stack->m_obj
 = v_res_3366_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3367_, lean_object* v_i_3368_, lean_object* v_bs_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
size_t v_sz_boxed_3378_; size_t v_i_boxed_3379_; lean_object* v_res_3380_; 
v_sz_boxed_3378_ = lean_unbox_usize(v_sz_3367_);
lean_dec(v_sz_3367_);
v_i_boxed_3379_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_res_3380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3378_, v_i_boxed_3379_, v_bs_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
return v_res_3380_;
}
}
lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v_merge_3401_; 
v_merge_3401_ = lean_ctor_get_uint8(v_a_3382_, 6);
if (v_merge_3401_ == 0)
{
v___y_3391_ = v_a_3382_;
v___y_3392_ = v_a_3383_;
v___y_3393_ = v_a_3384_;
v___y_3394_ = v_a_3385_;
v___y_3395_ = v_a_3386_;
v___y_3396_ = v_a_3387_;
v___y_3397_ = v_a_3388_;
goto v___jp_3390_;
}
else
{
uint8_t v_useContext_3402_; 
v_useContext_3402_ = lean_ctor_get_uint8(v_a_3382_, 7);
if (v_useContext_3402_ == 0)
{
v___y_3391_ = v_a_3382_;
v___y_3392_ = v_a_3383_;
v___y_3393_ = v_a_3384_;
v___y_3394_ = v_a_3385_;
v___y_3395_ = v_a_3386_;
v___y_3396_ = v_a_3387_;
v___y_3397_ = v_a_3388_;
goto v___jp_3390_;
}
else
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_dec_ref_known(v___x_3403_, 1);
v___y_3391_ = v_a_3382_;
v___y_3392_ = v_a_3383_;
v___y_3393_ = v_a_3384_;
v___y_3394_ = v_a_3385_;
v___y_3395_ = v_a_3386_;
v___y_3396_ = v_a_3387_;
v___y_3397_ = v_a_3388_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v_es_3381_);
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
v___jp_3390_:
{
size_t v_sz_3398_; size_t v___x_3399_; lean_object* v___x_3400_; 
v_sz_3398_ = lean_array_size(v_es_3381_);
v___x_3399_ = ((size_t)0ULL);
v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3398_, v___x_3399_, v_es_3381_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3400_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ExtractLets_extract_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_3381_ = stack[0].m_obj;
lean_object* v_a_3382_ = stack[1].m_obj;
lean_object* v_a_3383_ = stack[2].m_obj;
lean_object* v_a_3384_ = stack[3].m_obj;
lean_object* v_a_3385_ = stack[4].m_obj;
lean_object* v_a_3386_ = stack[5].m_obj;
lean_object* v_a_3387_ = stack[6].m_obj;
lean_object* v_a_3388_ = stack[7].m_obj;
lean_object* v_res_3412_;
v_res_3412_ = l_Lean_Meta_ExtractLets_extract(v_es_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
stack->m_obj
 = v_res_3412_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Meta_ExtractLets_extract(v_es_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
return v_res_3422_;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3423_, lean_object* v_x_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3423_, v_x_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
v_a_3439_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3430_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3430_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_3423_ = stack[0].m_obj;
lean_object* v_x_3424_ = stack[1].m_obj;
lean_object* v___y_3425_ = stack[2].m_obj;
lean_object* v___y_3426_ = stack[3].m_obj;
lean_object* v___y_3427_ = stack[4].m_obj;
lean_object* v___y_3428_ = stack[5].m_obj;
lean_object* v_res_3447_;
v_res_3447_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3423_, v_x_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
stack->m_obj
 = v_res_3447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3448_, lean_object* v_x_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3448_, v_x_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3455_;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3456_, lean_object* v_decls_3457_, lean_object* v_x_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3457_, v_x_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
return v___x_3464_;
}
}
LEAN_EXPORT void l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_3457_ = stack[1].m_obj;
lean_object* v_x_3458_ = stack[2].m_obj;
lean_object* v___y_3459_ = stack[3].m_obj;
lean_object* v___y_3460_ = stack[4].m_obj;
lean_object* v___y_3461_ = stack[5].m_obj;
lean_object* v___y_3462_ = stack[6].m_obj;
lean_object* v_res_3465_;
v_res_3465_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_box(0), v_decls_3457_, v_x_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
stack->m_obj
 = v_res_3465_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3466_, lean_object* v_decls_3467_, lean_object* v_x_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3466_, v_decls_3467_, v_x_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
return v_res_3474_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3475_, size_t v_i_3476_, lean_object* v_bs_3477_){
_start:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_usize_dec_lt(v_i_3476_, v_sz_3475_);
if (v___x_3478_ == 0)
{
return v_bs_3477_;
}
else
{
lean_object* v_v_3479_; lean_object* v___x_3480_; lean_object* v_bs_x27_3481_; lean_object* v___x_3482_; size_t v___x_3483_; size_t v___x_3484_; lean_object* v___x_3485_; 
v_v_3479_ = lean_array_uget(v_bs_3477_, v_i_3476_);
v___x_3480_ = lean_unsigned_to_nat(0u);
v_bs_x27_3481_ = lean_array_uset(v_bs_3477_, v_i_3476_, v___x_3480_);
v___x_3482_ = l_Lean_LocalDecl_fvarId(v_v_3479_);
lean_dec(v_v_3479_);
v___x_3483_ = ((size_t)1ULL);
v___x_3484_ = lean_usize_add(v_i_3476_, v___x_3483_);
v___x_3485_ = lean_array_uset(v_bs_x27_3481_, v_i_3476_, v___x_3482_);
v_i_3476_ = v___x_3484_;
v_bs_3477_ = v___x_3485_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3475_ = stack[0].m_num;
size_t v_i_3476_ = stack[1].m_num;
lean_object* v_bs_3477_ = stack[2].m_obj;
lean_object* v_res_3487_;
v_res_3487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3475_, v_i_3476_, v_bs_3477_);
stack->m_obj
 = v_res_3487_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3488_, lean_object* v_i_3489_, lean_object* v_bs_3490_){
_start:
{
size_t v_sz_boxed_3491_; size_t v_i_boxed_3492_; lean_object* v_res_3493_; 
v_sz_boxed_3491_ = lean_unbox_usize(v_sz_3488_);
lean_dec(v_sz_3488_);
v_i_boxed_3492_ = lean_unbox_usize(v_i_3489_);
lean_dec(v_i_3489_);
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3491_, v_i_boxed_3492_, v_bs_3490_);
return v_res_3493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = lean_box(0);
v___x_3495_ = lean_unsigned_to_nat(16u);
v___x_3496_ = lean_mk_array(v___x_3495_, v___x_3494_);
return v___x_3496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
lean_ctor_set(v___x_3499_, 1, v___x_3497_);
return v___x_3499_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3500_, lean_object* v_givenNames_3501_, lean_object* v_k_3502_, lean_object* v_config_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3510_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3511_, 0, v_givenNames_3501_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
lean_ctor_set(v___x_3511_, 2, v___x_3509_);
v___x_3512_ = lean_st_mk_ref(v___x_3511_);
v___x_3513_ = lean_st_mk_ref(v___x_3509_);
v___x_3514_ = l_Lean_Meta_ExtractLets_extract(v_es_3500_, v_config_3503_, v___x_3513_, v___x_3512_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v_givenNames_3518_; lean_object* v_decls_3519_; size_t v_sz_3520_; size_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; size_t v_sz_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = lean_st_ref_get(v___x_3513_);
lean_dec(v___x_3513_);
lean_dec(v___x_3516_);
v___x_3517_ = lean_st_ref_get(v___x_3512_);
lean_dec(v___x_3512_);
v_givenNames_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_givenNames_3518_);
v_decls_3519_ = lean_ctor_get(v___x_3517_, 1);
lean_inc_ref(v_decls_3519_);
lean_dec(v___x_3517_);
v_sz_3520_ = lean_array_size(v_decls_3519_);
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_3520_, v___x_3521_, v_decls_3519_);
lean_inc_ref(v___x_3522_);
v___x_3523_ = lean_array_to_list(v___x_3522_);
v_sz_3524_ = lean_array_size(v___x_3522_);
v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3524_, v___x_3521_, v___x_3522_);
v___x_3526_ = lean_apply_3(v_k_3502_, v___x_3525_, v_a_3515_, v_givenNames_3518_);
v___x_3527_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3523_, v___x_3526_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3527_;
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v___x_3513_);
lean_dec(v___x_3512_);
lean_dec_ref(v_k_3502_);
v_a_3528_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3514_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3514_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_3500_ = stack[0].m_obj;
lean_object* v_givenNames_3501_ = stack[1].m_obj;
lean_object* v_k_3502_ = stack[2].m_obj;
lean_object* v_config_3503_ = stack[3].m_obj;
lean_object* v_a_3504_ = stack[4].m_obj;
lean_object* v_a_3505_ = stack[5].m_obj;
lean_object* v_a_3506_ = stack[6].m_obj;
lean_object* v_a_3507_ = stack[7].m_obj;
lean_object* v_res_3536_;
v_res_3536_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3500_, v_givenNames_3501_, v_k_3502_, v_config_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
stack->m_obj
 = v_res_3536_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3537_, lean_object* v_givenNames_3538_, lean_object* v_k_3539_, lean_object* v_config_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3537_, v_givenNames_3538_, v_k_3539_, v_config_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec_ref(v_config_3540_);
return v_res_3546_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3547_, lean_object* v_es_3548_, lean_object* v_givenNames_3549_, lean_object* v_k_3550_, lean_object* v_config_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3548_, v_givenNames_3549_, v_k_3550_, v_config_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
return v___x_3557_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_3548_ = stack[1].m_obj;
lean_object* v_givenNames_3549_ = stack[2].m_obj;
lean_object* v_k_3550_ = stack[3].m_obj;
lean_object* v_config_3551_ = stack[4].m_obj;
lean_object* v_a_3552_ = stack[5].m_obj;
lean_object* v_a_3553_ = stack[6].m_obj;
lean_object* v_a_3554_ = stack[7].m_obj;
lean_object* v_a_3555_ = stack[8].m_obj;
lean_object* v_res_3558_;
v_res_3558_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_box(0), v_es_3548_, v_givenNames_3549_, v_k_3550_, v_config_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
stack->m_obj
 = v_res_3558_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3559_, lean_object* v_es_3560_, lean_object* v_givenNames_3561_, lean_object* v_k_3562_, lean_object* v_config_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3559_, v_es_3560_, v_givenNames_3561_, v_k_3562_, v_config_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec_ref(v_config_3563_);
return v_res_3569_;
}
}
lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3570_, lean_object* v_runInBase_3571_, lean_object* v_b_3572_, lean_object* v_c_3573_, lean_object* v_d_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = lean_apply_3(v_k_3570_, v_b_3572_, v_c_3573_, v_d_3574_);
lean_inc(v___y_3578_);
lean_inc_ref(v___y_3577_);
lean_inc(v___y_3576_);
lean_inc_ref(v___y_3575_);
v___x_3581_ = lean_apply_7(v_runInBase_3571_, lean_box(0), v___x_3580_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, lean_box(0));
return v___x_3581_;
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3570_ = stack[0].m_obj;
lean_object* v_runInBase_3571_ = stack[1].m_obj;
lean_object* v_b_3572_ = stack[2].m_obj;
lean_object* v_c_3573_ = stack[3].m_obj;
lean_object* v_d_3574_ = stack[4].m_obj;
lean_object* v___y_3575_ = stack[5].m_obj;
lean_object* v___y_3576_ = stack[6].m_obj;
lean_object* v___y_3577_ = stack[7].m_obj;
lean_object* v___y_3578_ = stack[8].m_obj;
lean_object* v_res_3582_;
v_res_3582_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3570_, v_runInBase_3571_, v_b_3572_, v_c_3573_, v_d_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
stack->m_obj
 = v_res_3582_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3583_, lean_object* v_runInBase_3584_, lean_object* v_b_3585_, lean_object* v_c_3586_, lean_object* v_d_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3583_, v_runInBase_3584_, v_b_3585_, v_c_3586_, v_d_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
return v_res_3593_;
}
}
lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3594_, lean_object* v_es_3595_, lean_object* v_givenNames_3596_, lean_object* v_config_3597_, lean_object* v_runInBase_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___f_3604_; lean_object* v___x_3605_; 
v___f_3604_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3604_, 0, v_k_3594_);
lean_closure_set(v___f_3604_, 1, v_runInBase_3598_);
v___x_3605_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3595_, v_givenNames_3596_, v___f_3604_, v_config_3597_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
return v___x_3605_;
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3594_ = stack[0].m_obj;
lean_object* v_es_3595_ = stack[1].m_obj;
lean_object* v_givenNames_3596_ = stack[2].m_obj;
lean_object* v_config_3597_ = stack[3].m_obj;
lean_object* v_runInBase_3598_ = stack[4].m_obj;
lean_object* v___y_3599_ = stack[5].m_obj;
lean_object* v___y_3600_ = stack[6].m_obj;
lean_object* v___y_3601_ = stack[7].m_obj;
lean_object* v___y_3602_ = stack[8].m_obj;
lean_object* v_res_3606_;
v_res_3606_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3594_, v_es_3595_, v_givenNames_3596_, v_config_3597_, v_runInBase_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
stack->m_obj
 = v_res_3606_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3607_, lean_object* v_es_3608_, lean_object* v_givenNames_3609_, lean_object* v_config_3610_, lean_object* v_runInBase_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3607_, v_es_3608_, v_givenNames_3609_, v_config_3610_, v_runInBase_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v_config_3610_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3618_, lean_object* v_inst_3619_, lean_object* v_es_3620_, lean_object* v_givenNames_3621_, lean_object* v_k_3622_, lean_object* v_config_3623_){
_start:
{
lean_object* v_toBind_3624_; lean_object* v_liftWith_3625_; lean_object* v_restoreM_3626_; lean_object* v___f_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v_toBind_3624_ = lean_ctor_get(v_inst_3618_, 1);
lean_inc(v_toBind_3624_);
lean_dec_ref(v_inst_3618_);
v_liftWith_3625_ = lean_ctor_get(v_inst_3619_, 0);
lean_inc(v_liftWith_3625_);
v_restoreM_3626_ = lean_ctor_get(v_inst_3619_, 1);
lean_inc(v_restoreM_3626_);
lean_dec_ref(v_inst_3619_);
v___f_3627_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3627_, 0, v_k_3622_);
lean_closure_set(v___f_3627_, 1, v_es_3620_);
lean_closure_set(v___f_3627_, 2, v_givenNames_3621_);
lean_closure_set(v___f_3627_, 3, v_config_3623_);
v___x_3628_ = lean_apply_2(v_liftWith_3625_, lean_box(0), v___f_3627_);
v___x_3629_ = lean_apply_1(v_restoreM_3626_, lean_box(0));
v___x_3630_ = lean_apply_4(v_toBind_3624_, lean_box(0), lean_box(0), v___x_3628_, v___x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3631_, lean_object* v_00_u03b1_3632_, lean_object* v_inst_3633_, lean_object* v_inst_3634_, lean_object* v_es_3635_, lean_object* v_givenNames_3636_, lean_object* v_k_3637_, lean_object* v_config_3638_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_Meta_extractLets___redArg(v_inst_3633_, v_inst_3634_, v_es_3635_, v_givenNames_3636_, v_k_3637_, v_config_3638_);
return v___x_3639_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3641_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3642_ = lean_box(0);
v___x_3643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___x_3641_);
lean_ctor_set(v___x_3643_, 2, v___x_3640_);
return v___x_3643_;
}
}
lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3644_, lean_object* v_config_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_){
_start:
{
uint8_t v_proofs_3651_; uint8_t v_types_3652_; uint8_t v_implicits_3653_; uint8_t v_descend_3654_; uint8_t v_underBinder_3655_; uint8_t v_usedOnly_3656_; uint8_t v_merge_3657_; uint8_t v_useContext_3658_; uint8_t v_preserveBinderNames_3659_; uint8_t v_lift_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3699_; 
v_proofs_3651_ = lean_ctor_get_uint8(v_config_3645_, 0);
v_types_3652_ = lean_ctor_get_uint8(v_config_3645_, 1);
v_implicits_3653_ = lean_ctor_get_uint8(v_config_3645_, 2);
v_descend_3654_ = lean_ctor_get_uint8(v_config_3645_, 3);
v_underBinder_3655_ = lean_ctor_get_uint8(v_config_3645_, 4);
v_usedOnly_3656_ = lean_ctor_get_uint8(v_config_3645_, 5);
v_merge_3657_ = lean_ctor_get_uint8(v_config_3645_, 6);
v_useContext_3658_ = lean_ctor_get_uint8(v_config_3645_, 7);
v_preserveBinderNames_3659_ = lean_ctor_get_uint8(v_config_3645_, 9);
v_lift_3660_ = lean_ctor_get_uint8(v_config_3645_, 10);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_config_3645_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3662_ = v_config_3645_;
v_isShared_3663_ = v_isSharedCheck_3699_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v_config_3645_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3699_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; uint8_t v___x_3668_; lean_object* v___x_3670_; 
v___x_3664_ = l_Lean_instInhabitedExpr;
v___x_3665_ = lean_unsigned_to_nat(1u);
v___x_3666_ = lean_mk_empty_array_with_capacity(v___x_3665_);
v___x_3667_ = lean_array_push(v___x_3666_, v_e_3644_);
v___x_3668_ = 1;
if (v_isShared_3663_ == 0)
{
v___x_3670_ = v___x_3662_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 0, v_proofs_3651_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 1, v_types_3652_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 2, v_implicits_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 3, v_descend_3654_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 4, v_underBinder_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 5, v_usedOnly_3656_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 6, v_merge_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 7, v_useContext_3658_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 9, v_preserveBinderNames_3659_);
lean_ctor_set_uint8(v_reuseFailAlloc_3698_, 10, v_lift_3660_);
v___x_3670_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_ctor_set_uint8(v___x_3670_, 8, v___x_3668_);
v___x_3671_ = lean_unsigned_to_nat(0u);
v___x_3672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3673_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3674_ = lean_st_mk_ref(v___x_3673_);
v___x_3675_ = lean_st_mk_ref(v___x_3672_);
v___x_3676_ = l_Lean_Meta_ExtractLets_extract(v___x_3667_, v___x_3670_, v___x_3675_, v___x_3674_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
lean_dec_ref(v___x_3670_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3689_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3689_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3689_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v_decls_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3681_ = lean_st_ref_get(v___x_3675_);
lean_dec(v___x_3675_);
lean_dec(v___x_3681_);
v___x_3682_ = lean_st_ref_get(v___x_3674_);
lean_dec(v___x_3674_);
v_decls_3683_ = lean_ctor_get(v___x_3682_, 1);
lean_inc_ref(v_decls_3683_);
lean_dec(v___x_3682_);
v___x_3684_ = lean_array_get(v___x_3664_, v_a_3677_, v___x_3671_);
lean_dec(v_a_3677_);
v___x_3685_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3683_, v___x_3684_);
lean_dec_ref(v_decls_3683_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3685_);
v___x_3687_ = v___x_3679_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v___x_3675_);
lean_dec(v___x_3674_);
v_a_3690_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3676_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3676_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_liftLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3644_ = stack[0].m_obj;
lean_object* v_config_3645_ = stack[1].m_obj;
lean_object* v_a_3646_ = stack[2].m_obj;
lean_object* v_a_3647_ = stack[3].m_obj;
lean_object* v_a_3648_ = stack[4].m_obj;
lean_object* v_a_3649_ = stack[5].m_obj;
lean_object* v_res_3700_;
v_res_3700_ = l_Lean_Meta_liftLets(v_e_3644_, v_config_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
stack->m_obj
 = v_res_3700_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3701_, lean_object* v_config_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Meta_liftLets(v_e_3701_, v_config_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
return v_res_3708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3711_ = l_Lean_stringToMessageData(v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3714_, lean_object* v_mvarId_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3722_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3714_, v_mvarId_3715_, v___x_3721_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v___x_3722_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tactic_3714_ = stack[0].m_obj;
lean_object* v_mvarId_3715_ = stack[1].m_obj;
lean_object* v_a_3716_ = stack[2].m_obj;
lean_object* v_a_3717_ = stack[3].m_obj;
lean_object* v_a_3718_ = stack[4].m_obj;
lean_object* v_a_3719_ = stack[5].m_obj;
lean_object* v_res_3723_;
v_res_3723_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3714_, v_mvarId_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
stack->m_obj
 = v_res_3723_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3724_, lean_object* v_mvarId_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3724_, v_mvarId_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
return v_res_3731_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3732_, lean_object* v_tactic_3733_, lean_object* v_mvarId_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3733_, v_mvarId_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress_0interp(lean_interpreter_value* stack)
{
lean_object* v_tactic_3733_ = stack[1].m_obj;
lean_object* v_mvarId_3734_ = stack[2].m_obj;
lean_object* v_a_3735_ = stack[3].m_obj;
lean_object* v_a_3736_ = stack[4].m_obj;
lean_object* v_a_3737_ = stack[5].m_obj;
lean_object* v_a_3738_ = stack[6].m_obj;
lean_object* v_res_3741_;
v_res_3741_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_box(0), v_tactic_3733_, v_mvarId_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
stack->m_obj
 = v_res_3741_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3742_, lean_object* v_tactic_3743_, lean_object* v_mvarId_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3742_, v_tactic_3743_, v_mvarId_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_);
lean_dec(v_a_3748_);
lean_dec_ref(v_a_3747_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
return v_res_3750_;
}
}
lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3751_, lean_object* v_b_3752_, lean_object* v_c_3753_, lean_object* v_d_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; 
lean_inc(v___y_3758_);
lean_inc_ref(v___y_3757_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
v___x_3760_ = lean_apply_8(v_k_3751_, v_b_3752_, v_c_3753_, v_d_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, lean_box(0));
return v___x_3760_;
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3751_ = stack[0].m_obj;
lean_object* v_b_3752_ = stack[1].m_obj;
lean_object* v_c_3753_ = stack[2].m_obj;
lean_object* v_d_3754_ = stack[3].m_obj;
lean_object* v___y_3755_ = stack[4].m_obj;
lean_object* v___y_3756_ = stack[5].m_obj;
lean_object* v___y_3757_ = stack[6].m_obj;
lean_object* v___y_3758_ = stack[7].m_obj;
lean_object* v_res_3761_;
v_res_3761_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3751_, v_b_3752_, v_c_3753_, v_d_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
stack->m_obj
 = v_res_3761_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3762_, lean_object* v_b_3763_, lean_object* v_c_3764_, lean_object* v_d_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3762_, v_b_3763_, v_c_3764_, v_d_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
return v_res_3771_;
}
}
lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3772_, lean_object* v_givenNames_3773_, lean_object* v_k_3774_, lean_object* v_config_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___f_3781_; lean_object* v___x_3782_; 
v___f_3781_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3781_, 0, v_k_3774_);
v___x_3782_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3772_, v_givenNames_3773_, v___f_3781_, v_config_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
v_a_3791_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3782_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3782_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_3772_ = stack[0].m_obj;
lean_object* v_givenNames_3773_ = stack[1].m_obj;
lean_object* v_k_3774_ = stack[2].m_obj;
lean_object* v_config_3775_ = stack[3].m_obj;
lean_object* v___y_3776_ = stack[4].m_obj;
lean_object* v___y_3777_ = stack[5].m_obj;
lean_object* v___y_3778_ = stack[6].m_obj;
lean_object* v___y_3779_ = stack[7].m_obj;
lean_object* v_res_3799_;
v_res_3799_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3772_, v_givenNames_3773_, v_k_3774_, v_config_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
stack->m_obj
 = v_res_3799_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3800_, lean_object* v_givenNames_3801_, lean_object* v_k_3802_, lean_object* v_config_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3800_, v_givenNames_3801_, v_k_3802_, v_config_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_config_3803_);
return v_res_3809_;
}
}
lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3810_, lean_object* v_es_3811_, lean_object* v_givenNames_3812_, lean_object* v_k_3813_, lean_object* v_config_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3811_, v_givenNames_3812_, v_k_3813_, v_config_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
return v___x_3820_;
}
}
LEAN_EXPORT void l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_3811_ = stack[1].m_obj;
lean_object* v_givenNames_3812_ = stack[2].m_obj;
lean_object* v_k_3813_ = stack[3].m_obj;
lean_object* v_config_3814_ = stack[4].m_obj;
lean_object* v___y_3815_ = stack[5].m_obj;
lean_object* v___y_3816_ = stack[6].m_obj;
lean_object* v___y_3817_ = stack[7].m_obj;
lean_object* v___y_3818_ = stack[8].m_obj;
lean_object* v_res_3821_;
v_res_3821_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_box(0), v_es_3811_, v_givenNames_3812_, v_k_3813_, v_config_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
stack->m_obj
 = v_res_3821_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3822_, lean_object* v_es_3823_, lean_object* v_givenNames_3824_, lean_object* v_k_3825_, lean_object* v_config_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3822_, v_es_3823_, v_givenNames_3824_, v_k_3825_, v_config_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec_ref(v_config_3826_);
return v_res_3832_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3833_, v_x_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3840_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3840_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3833_ = stack[0].m_obj;
lean_object* v_x_3834_ = stack[1].m_obj;
lean_object* v___y_3835_ = stack[2].m_obj;
lean_object* v___y_3836_ = stack[3].m_obj;
lean_object* v___y_3837_ = stack[4].m_obj;
lean_object* v___y_3838_ = stack[5].m_obj;
lean_object* v_res_3857_;
v_res_3857_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3833_, v_x_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
stack->m_obj
 = v_res_3857_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3858_, lean_object* v_x_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3858_, v_x_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
return v_res_3865_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3866_, lean_object* v_mvarId_3867_, lean_object* v_x_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3867_, v_x_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3867_ = stack[1].m_obj;
lean_object* v_x_3868_ = stack[2].m_obj;
lean_object* v___y_3869_ = stack[3].m_obj;
lean_object* v___y_3870_ = stack[4].m_obj;
lean_object* v___y_3871_ = stack[5].m_obj;
lean_object* v___y_3872_ = stack[6].m_obj;
lean_object* v_res_3875_;
v_res_3875_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_box(0), v_mvarId_3867_, v_x_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
stack->m_obj
 = v_res_3875_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3876_, lean_object* v_mvarId_3877_, lean_object* v_x_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3876_, v_mvarId_3877_, v_x_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3885_, lean_object* v_x_3886_, lean_object* v_x_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v_ks_3889_; lean_object* v_vs_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3914_; 
v_ks_3889_ = lean_ctor_get(v_x_3885_, 0);
v_vs_3890_ = lean_ctor_get(v_x_3885_, 1);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_x_3885_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3892_ = v_x_3885_;
v_isShared_3893_ = v_isSharedCheck_3914_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_vs_3890_);
lean_inc(v_ks_3889_);
lean_dec(v_x_3885_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3914_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3894_ = lean_array_get_size(v_ks_3889_);
v___x_3895_ = lean_nat_dec_lt(v_x_3886_, v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3899_; 
lean_dec(v_x_3886_);
v___x_3896_ = lean_array_push(v_ks_3889_, v_x_3887_);
v___x_3897_ = lean_array_push(v_vs_3890_, v_x_3888_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 1, v___x_3897_);
lean_ctor_set(v___x_3892_, 0, v___x_3896_);
v___x_3899_ = v___x_3892_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___x_3897_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
else
{
lean_object* v_k_x27_3901_; uint8_t v___x_3902_; 
v_k_x27_3901_ = lean_array_fget_borrowed(v_ks_3889_, v_x_3886_);
v___x_3902_ = l_Lean_instBEqMVarId_beq(v_x_3887_, v_k_x27_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3904_; 
if (v_isShared_3893_ == 0)
{
v___x_3904_ = v___x_3892_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_ks_3889_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_vs_3890_);
v___x_3904_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = lean_nat_add(v_x_3886_, v___x_3905_);
lean_dec(v_x_3886_);
v_x_3885_ = v___x_3904_;
v_x_3886_ = v___x_3906_;
goto _start;
}
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3909_ = lean_array_fset(v_ks_3889_, v_x_3886_, v_x_3887_);
v___x_3910_ = lean_array_fset(v_vs_3890_, v_x_3886_, v_x_3888_);
lean_dec(v_x_3886_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 1, v___x_3910_);
lean_ctor_set(v___x_3892_, 0, v___x_3909_);
v___x_3912_ = v___x_3892_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3915_, lean_object* v_k_3916_, lean_object* v_v_3917_){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3915_, v___x_3918_, v_k_3916_, v_v_3917_);
return v___x_3919_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3920_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3921_, size_t v_x_3922_, size_t v_x_3923_, lean_object* v_x_3924_, lean_object* v_x_3925_){
_start:
{
if (lean_obj_tag(v_x_3921_) == 0)
{
lean_object* v_es_3926_; size_t v___x_3927_; size_t v___x_3928_; lean_object* v_j_3929_; lean_object* v___x_3930_; uint8_t v___x_3931_; 
v_es_3926_ = lean_ctor_get(v_x_3921_, 0);
v___x_3927_ = ((size_t)31ULL);
v___x_3928_ = lean_usize_land(v_x_3922_, v___x_3927_);
v_j_3929_ = lean_usize_to_nat(v___x_3928_);
v___x_3930_ = lean_array_get_size(v_es_3926_);
v___x_3931_ = lean_nat_dec_lt(v_j_3929_, v___x_3930_);
if (v___x_3931_ == 0)
{
lean_dec(v_j_3929_);
lean_dec(v_x_3925_);
lean_dec(v_x_3924_);
return v_x_3921_;
}
else
{
lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3970_; 
lean_inc_ref(v_es_3926_);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_x_3921_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; 
v_unused_3971_ = lean_ctor_get(v_x_3921_, 0);
lean_dec(v_unused_3971_);
v___x_3933_ = v_x_3921_;
v_isShared_3934_ = v_isSharedCheck_3970_;
goto v_resetjp_3932_;
}
else
{
lean_dec(v_x_3921_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3970_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v_v_3935_; lean_object* v___x_3936_; lean_object* v_xs_x27_3937_; lean_object* v___y_3939_; 
v_v_3935_ = lean_array_fget(v_es_3926_, v_j_3929_);
v___x_3936_ = lean_box(0);
v_xs_x27_3937_ = lean_array_fset(v_es_3926_, v_j_3929_, v___x_3936_);
switch(lean_obj_tag(v_v_3935_))
{
case 0:
{
lean_object* v_key_3944_; lean_object* v_val_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3955_; 
v_key_3944_ = lean_ctor_get(v_v_3935_, 0);
v_val_3945_ = lean_ctor_get(v_v_3935_, 1);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_v_3935_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3947_ = v_v_3935_;
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_val_3945_);
lean_inc(v_key_3944_);
lean_dec(v_v_3935_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
uint8_t v___x_3949_; 
v___x_3949_ = l_Lean_instBEqMVarId_beq(v_x_3924_, v_key_3944_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_del_object(v___x_3947_);
v___x_3950_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3944_, v_val_3945_, v_x_3924_, v_x_3925_);
v___x_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
v___y_3939_ = v___x_3951_;
goto v___jp_3938_;
}
else
{
lean_object* v___x_3953_; 
lean_dec(v_val_3945_);
lean_dec(v_key_3944_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 1, v_x_3925_);
lean_ctor_set(v___x_3947_, 0, v_x_3924_);
v___x_3953_ = v___x_3947_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_x_3924_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_x_3925_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
v___y_3939_ = v___x_3953_;
goto v___jp_3938_;
}
}
}
}
case 1:
{
lean_object* v_node_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3968_; 
v_node_3956_ = lean_ctor_get(v_v_3935_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_v_3935_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3958_ = v_v_3935_;
v_isShared_3959_ = v_isSharedCheck_3968_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_node_3956_);
lean_dec(v_v_3935_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3968_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
size_t v___x_3960_; size_t v___x_3961_; size_t v___x_3962_; size_t v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3960_ = ((size_t)5ULL);
v___x_3961_ = lean_usize_shift_right(v_x_3922_, v___x_3960_);
v___x_3962_ = ((size_t)1ULL);
v___x_3963_ = lean_usize_add(v_x_3923_, v___x_3962_);
v___x_3964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3956_, v___x_3961_, v___x_3963_, v_x_3924_, v_x_3925_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3964_);
v___x_3966_ = v___x_3958_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
v___y_3939_ = v___x_3966_;
goto v___jp_3938_;
}
}
}
default: 
{
lean_object* v___x_3969_; 
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v_x_3924_);
lean_ctor_set(v___x_3969_, 1, v_x_3925_);
v___y_3939_ = v___x_3969_;
goto v___jp_3938_;
}
}
v___jp_3938_:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3940_ = lean_array_fset(v_xs_x27_3937_, v_j_3929_, v___y_3939_);
lean_dec(v_j_3929_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3940_);
v___x_3942_ = v___x_3933_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
else
{
lean_object* v_ks_3972_; lean_object* v_vs_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3991_; 
v_ks_3972_ = lean_ctor_get(v_x_3921_, 0);
v_vs_3973_ = lean_ctor_get(v_x_3921_, 1);
v_isSharedCheck_3991_ = !lean_is_exclusive(v_x_3921_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3975_ = v_x_3921_;
v_isShared_3976_ = v_isSharedCheck_3991_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_vs_3973_);
lean_inc(v_ks_3972_);
lean_dec(v_x_3921_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3991_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_ks_3972_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_vs_3973_);
v___x_3978_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v_newNode_3979_; size_t v___x_3980_; uint8_t v___x_3981_; 
v_newNode_3979_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3978_, v_x_3924_, v_x_3925_);
v___x_3980_ = ((size_t)7ULL);
v___x_3981_ = lean_usize_dec_le(v___x_3980_, v_x_3923_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3982_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3979_);
v___x_3983_ = lean_unsigned_to_nat(4u);
v___x_3984_ = lean_nat_dec_lt(v___x_3982_, v___x_3983_);
lean_dec(v___x_3982_);
if (v___x_3984_ == 0)
{
lean_object* v_ks_3985_; lean_object* v_vs_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_ks_3985_ = lean_ctor_get(v_newNode_3979_, 0);
lean_inc_ref(v_ks_3985_);
v_vs_3986_ = lean_ctor_get(v_newNode_3979_, 1);
lean_inc_ref(v_vs_3986_);
lean_dec_ref(v_newNode_3979_);
v___x_3987_ = lean_unsigned_to_nat(0u);
v___x_3988_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3923_, v_ks_3985_, v_vs_3986_, v___x_3987_, v___x_3988_);
lean_dec_ref(v_vs_3986_);
lean_dec_ref(v_ks_3985_);
return v___x_3989_;
}
else
{
return v_newNode_3979_;
}
}
else
{
return v_newNode_3979_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3921_ = stack[0].m_obj;
size_t v_x_3922_ = stack[1].m_num;
size_t v_x_3923_ = stack[2].m_num;
lean_object* v_x_3924_ = stack[3].m_obj;
lean_object* v_x_3925_ = stack[4].m_obj;
lean_object* v_res_3992_;
v_res_3992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3921_, v_x_3922_, v_x_3923_, v_x_3924_, v_x_3925_);
stack->m_obj
 = v_res_3992_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3993_, lean_object* v_keys_3994_, lean_object* v_vals_3995_, lean_object* v_i_3996_, lean_object* v_entries_3997_){
_start:
{
lean_object* v___x_3998_; uint8_t v___x_3999_; 
v___x_3998_ = lean_array_get_size(v_keys_3994_);
v___x_3999_ = lean_nat_dec_lt(v_i_3996_, v___x_3998_);
if (v___x_3999_ == 0)
{
lean_dec(v_i_3996_);
return v_entries_3997_;
}
else
{
lean_object* v_k_4000_; lean_object* v_v_4001_; uint64_t v___x_4002_; size_t v_h_4003_; size_t v___x_4004_; lean_object* v___x_4005_; size_t v___x_4006_; size_t v___x_4007_; size_t v___x_4008_; size_t v_h_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_k_4000_ = lean_array_fget_borrowed(v_keys_3994_, v_i_3996_);
v_v_4001_ = lean_array_fget_borrowed(v_vals_3995_, v_i_3996_);
v___x_4002_ = l_Lean_instHashableMVarId_hash(v_k_4000_);
v_h_4003_ = lean_uint64_to_usize(v___x_4002_);
v___x_4004_ = ((size_t)5ULL);
v___x_4005_ = lean_unsigned_to_nat(1u);
v___x_4006_ = ((size_t)1ULL);
v___x_4007_ = lean_usize_sub(v_depth_3993_, v___x_4006_);
v___x_4008_ = lean_usize_mul(v___x_4004_, v___x_4007_);
v_h_4009_ = lean_usize_shift_right(v_h_4003_, v___x_4008_);
v___x_4010_ = lean_nat_add(v_i_3996_, v___x_4005_);
lean_dec(v_i_3996_);
lean_inc(v_v_4001_);
lean_inc(v_k_4000_);
v___x_4011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3997_, v_h_4009_, v_depth_3993_, v_k_4000_, v_v_4001_);
v_i_3996_ = v___x_4010_;
v_entries_3997_ = v___x_4011_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3993_ = stack[0].m_num;
lean_object* v_keys_3994_ = stack[1].m_obj;
lean_object* v_vals_3995_ = stack[2].m_obj;
lean_object* v_i_3996_ = stack[3].m_obj;
lean_object* v_entries_3997_ = stack[4].m_obj;
lean_object* v_res_4013_;
v_res_4013_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_3993_, v_keys_3994_, v_vals_3995_, v_i_3996_, v_entries_3997_);
stack->m_obj
 = v_res_4013_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_4014_, lean_object* v_keys_4015_, lean_object* v_vals_4016_, lean_object* v_i_4017_, lean_object* v_entries_4018_){
_start:
{
size_t v_depth_boxed_4019_; lean_object* v_res_4020_; 
v_depth_boxed_4019_ = lean_unbox_usize(v_depth_4014_);
lean_dec(v_depth_4014_);
v_res_4020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_4019_, v_keys_4015_, v_vals_4016_, v_i_4017_, v_entries_4018_);
lean_dec_ref(v_vals_4016_);
lean_dec_ref(v_keys_4015_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_, lean_object* v_x_4024_, lean_object* v_x_4025_){
_start:
{
size_t v_x_2421__boxed_4026_; size_t v_x_2422__boxed_4027_; lean_object* v_res_4028_; 
v_x_2421__boxed_4026_ = lean_unbox_usize(v_x_4022_);
lean_dec(v_x_4022_);
v_x_2422__boxed_4027_ = lean_unbox_usize(v_x_4023_);
lean_dec(v_x_4023_);
v_res_4028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4021_, v_x_2421__boxed_4026_, v_x_2422__boxed_4027_, v_x_4024_, v_x_4025_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_4029_, lean_object* v_x_4030_, lean_object* v_x_4031_){
_start:
{
uint64_t v___x_4032_; size_t v___x_4033_; size_t v___x_4034_; lean_object* v___x_4035_; 
v___x_4032_ = l_Lean_instHashableMVarId_hash(v_x_4030_);
v___x_4033_ = lean_uint64_to_usize(v___x_4032_);
v___x_4034_ = ((size_t)1ULL);
v___x_4035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4029_, v___x_4033_, v___x_4034_, v_x_4030_, v_x_4031_);
return v___x_4035_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_4036_, lean_object* v_val_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; lean_object* v_mctx_4041_; lean_object* v_cache_4042_; lean_object* v_zetaDeltaFVarIds_4043_; lean_object* v_postponed_4044_; lean_object* v_diag_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4075_; 
v___x_4040_ = lean_st_ref_take(v___y_4038_);
v_mctx_4041_ = lean_ctor_get(v___x_4040_, 0);
v_cache_4042_ = lean_ctor_get(v___x_4040_, 1);
v_zetaDeltaFVarIds_4043_ = lean_ctor_get(v___x_4040_, 2);
v_postponed_4044_ = lean_ctor_get(v___x_4040_, 3);
v_diag_4045_ = lean_ctor_get(v___x_4040_, 4);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4047_ = v___x_4040_;
v_isShared_4048_ = v_isSharedCheck_4075_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_diag_4045_);
lean_inc(v_postponed_4044_);
lean_inc(v_zetaDeltaFVarIds_4043_);
lean_inc(v_cache_4042_);
lean_inc(v_mctx_4041_);
lean_dec(v___x_4040_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4075_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v_depth_4049_; lean_object* v_levelAssignDepth_4050_; lean_object* v_lmvarCounter_4051_; lean_object* v_mvarCounter_4052_; lean_object* v_lDecls_4053_; lean_object* v_decls_4054_; lean_object* v_userNames_4055_; lean_object* v_lAssignment_4056_; lean_object* v_eAssignment_4057_; lean_object* v_dAssignment_4058_; lean_object* v_instanceTypedMVars_4059_; lean_object* v_synthNormMemo_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4074_; 
v_depth_4049_ = lean_ctor_get(v_mctx_4041_, 0);
v_levelAssignDepth_4050_ = lean_ctor_get(v_mctx_4041_, 1);
v_lmvarCounter_4051_ = lean_ctor_get(v_mctx_4041_, 2);
v_mvarCounter_4052_ = lean_ctor_get(v_mctx_4041_, 3);
v_lDecls_4053_ = lean_ctor_get(v_mctx_4041_, 4);
v_decls_4054_ = lean_ctor_get(v_mctx_4041_, 5);
v_userNames_4055_ = lean_ctor_get(v_mctx_4041_, 6);
v_lAssignment_4056_ = lean_ctor_get(v_mctx_4041_, 7);
v_eAssignment_4057_ = lean_ctor_get(v_mctx_4041_, 8);
v_dAssignment_4058_ = lean_ctor_get(v_mctx_4041_, 9);
v_instanceTypedMVars_4059_ = lean_ctor_get(v_mctx_4041_, 10);
v_synthNormMemo_4060_ = lean_ctor_get(v_mctx_4041_, 11);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_mctx_4041_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4062_ = v_mctx_4041_;
v_isShared_4063_ = v_isSharedCheck_4074_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_synthNormMemo_4060_);
lean_inc(v_instanceTypedMVars_4059_);
lean_inc(v_dAssignment_4058_);
lean_inc(v_eAssignment_4057_);
lean_inc(v_lAssignment_4056_);
lean_inc(v_userNames_4055_);
lean_inc(v_decls_4054_);
lean_inc(v_lDecls_4053_);
lean_inc(v_mvarCounter_4052_);
lean_inc(v_lmvarCounter_4051_);
lean_inc(v_levelAssignDepth_4050_);
lean_inc(v_depth_4049_);
lean_dec(v_mctx_4041_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4074_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4067_; 
v___x_4064_ = lean_box(0);
v___x_4065_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_4057_, v_mvarId_4036_, v_val_4037_);
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 8, v___x_4065_);
v___x_4067_ = v___x_4062_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_depth_4049_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_levelAssignDepth_4050_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_lmvarCounter_4051_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_mvarCounter_4052_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v_lDecls_4053_);
lean_ctor_set(v_reuseFailAlloc_4073_, 5, v_decls_4054_);
lean_ctor_set(v_reuseFailAlloc_4073_, 6, v_userNames_4055_);
lean_ctor_set(v_reuseFailAlloc_4073_, 7, v_lAssignment_4056_);
lean_ctor_set(v_reuseFailAlloc_4073_, 8, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4073_, 9, v_dAssignment_4058_);
lean_ctor_set(v_reuseFailAlloc_4073_, 10, v_instanceTypedMVars_4059_);
lean_ctor_set(v_reuseFailAlloc_4073_, 11, v_synthNormMemo_4060_);
v___x_4067_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4069_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___x_4067_);
v___x_4069_ = v___x_4047_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_cache_4042_);
lean_ctor_set(v_reuseFailAlloc_4072_, 2, v_zetaDeltaFVarIds_4043_);
lean_ctor_set(v_reuseFailAlloc_4072_, 3, v_postponed_4044_);
lean_ctor_set(v_reuseFailAlloc_4072_, 4, v_diag_4045_);
v___x_4069_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = lean_st_ref_put(v___y_4038_, v___x_4069_);
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4064_);
return v___x_4071_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4036_ = stack[0].m_obj;
lean_object* v_val_4037_ = stack[1].m_obj;
lean_object* v___y_4038_ = stack[2].m_obj;
lean_object* v_res_4076_;
v_res_4076_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4036_, v_val_4037_, v___y_4038_);
stack->m_obj
 = v_res_4076_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4077_, lean_object* v_val_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4077_, v_val_4078_, v___y_4079_);
lean_dec(v___y_4079_);
return v_res_4081_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4082_, size_t v_i_4083_, lean_object* v_bs_4084_){
_start:
{
uint8_t v___x_4085_; 
v___x_4085_ = lean_usize_dec_lt(v_i_4083_, v_sz_4082_);
if (v___x_4085_ == 0)
{
return v_bs_4084_;
}
else
{
lean_object* v_v_4086_; lean_object* v___x_4087_; lean_object* v_bs_x27_4088_; lean_object* v___x_4089_; size_t v___x_4090_; size_t v___x_4091_; lean_object* v___x_4092_; 
v_v_4086_ = lean_array_uget(v_bs_4084_, v_i_4083_);
v___x_4087_ = lean_unsigned_to_nat(0u);
v_bs_x27_4088_ = lean_array_uset(v_bs_4084_, v_i_4083_, v___x_4087_);
v___x_4089_ = l_Lean_Expr_fvar___override(v_v_4086_);
v___x_4090_ = ((size_t)1ULL);
v___x_4091_ = lean_usize_add(v_i_4083_, v___x_4090_);
v___x_4092_ = lean_array_uset(v_bs_x27_4088_, v_i_4083_, v___x_4089_);
v_i_4083_ = v___x_4091_;
v_bs_4084_ = v___x_4092_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4082_ = stack[0].m_num;
size_t v_i_4083_ = stack[1].m_num;
lean_object* v_bs_4084_ = stack[2].m_obj;
lean_object* v_res_4094_;
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4082_, v_i_4083_, v_bs_4084_);
stack->m_obj
 = v_res_4094_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4095_, lean_object* v_i_4096_, lean_object* v_bs_4097_){
_start:
{
size_t v_sz_boxed_4098_; size_t v_i_boxed_4099_; lean_object* v_res_4100_; 
v_sz_boxed_4098_ = lean_unbox_usize(v_sz_4095_);
lean_dec(v_sz_4095_);
v_i_boxed_4099_ = lean_unbox_usize(v_i_4096_);
lean_dec(v_i_4096_);
v_res_4100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4098_, v_i_boxed_4099_, v_bs_4097_);
return v_res_4100_;
}
}
lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4101_, lean_object* v_mvarId_4102_, lean_object* v_a_4103_, lean_object* v___x_4104_, lean_object* v_fvarIds_4105_, lean_object* v_es_4106_, lean_object* v_givenNames_x27_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = lean_array_get_borrowed(v___x_4101_, v_es_4106_, v___x_4113_);
v___x_4164_ = lean_array_get_size(v_fvarIds_4105_);
v___x_4165_ = lean_nat_dec_eq(v___x_4164_, v___x_4113_);
if (v___x_4165_ == 0)
{
lean_dec(v___x_4104_);
goto v___jp_4115_;
}
else
{
uint8_t v___x_4166_; 
v___x_4166_ = lean_expr_eqv(v_a_4103_, v___x_4114_);
if (v___x_4166_ == 0)
{
lean_dec(v___x_4104_);
goto v___jp_4115_;
}
else
{
lean_object* v___x_4167_; 
lean_inc(v_mvarId_4102_);
v___x_4167_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4104_, v_mvarId_4102_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_dec_ref_known(v___x_4167_, 1);
goto v___jp_4115_;
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_givenNames_x27_4107_);
lean_dec_ref(v_fvarIds_4105_);
lean_dec(v_mvarId_4102_);
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4167_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
}
v___jp_4115_:
{
lean_object* v___x_4116_; 
lean_inc(v_mvarId_4102_);
v___x_4116_ = l_Lean_MVarId_getTag(v_mvarId_4102_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref_known(v___x_4116_, 1);
lean_inc(v___x_4114_);
v___x_4118_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4114_, v_a_4117_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; size_t v_sz_4120_; size_t v___x_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; uint8_t v___x_4124_; uint8_t v___x_4125_; lean_object* v___x_4126_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc_n(v_a_4119_, 2);
lean_dec_ref_known(v___x_4118_, 1);
v_sz_4120_ = lean_array_size(v_fvarIds_4105_);
v___x_4121_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4105_);
v___x_4122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4120_, v___x_4121_, v_fvarIds_4105_);
v___x_4123_ = 0;
v___x_4124_ = 1;
v___x_4125_ = 1;
v___x_4126_ = l_Lean_Meta_mkLetFVars(v___x_4122_, v_a_4119_, v___x_4123_, v___x_4124_, v___x_4125_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec_ref(v___x_4122_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4138_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v___x_4128_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4102_, v_a_4127_, v___y_4109_);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v___x_4128_, 0);
lean_dec(v_unused_4139_);
v___x_4130_ = v___x_4128_;
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
else
{
lean_dec(v___x_4128_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v_fvarIds_4105_);
lean_ctor_set(v___x_4132_, 1, v_givenNames_x27_4107_);
v___x_4133_ = l_Lean_Expr_mvarId_x21(v_a_4119_);
lean_dec(v_a_4119_);
v___x_4134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4134_);
v___x_4136_ = v___x_4130_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v_a_4119_);
lean_dec(v_givenNames_x27_4107_);
lean_dec_ref(v_fvarIds_4105_);
lean_dec(v_mvarId_4102_);
v_a_4140_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4126_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4126_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec(v_givenNames_x27_4107_);
lean_dec_ref(v_fvarIds_4105_);
lean_dec(v_mvarId_4102_);
v_a_4148_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4118_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4118_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec(v_givenNames_x27_4107_);
lean_dec_ref(v_fvarIds_4105_);
lean_dec(v_mvarId_4102_);
v_a_4156_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4116_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4116_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4101_ = stack[0].m_obj;
lean_object* v_mvarId_4102_ = stack[1].m_obj;
lean_object* v_a_4103_ = stack[2].m_obj;
lean_object* v___x_4104_ = stack[3].m_obj;
lean_object* v_fvarIds_4105_ = stack[4].m_obj;
lean_object* v_es_4106_ = stack[5].m_obj;
lean_object* v_givenNames_x27_4107_ = stack[6].m_obj;
lean_object* v___y_4108_ = stack[7].m_obj;
lean_object* v___y_4109_ = stack[8].m_obj;
lean_object* v___y_4110_ = stack[9].m_obj;
lean_object* v___y_4111_ = stack[10].m_obj;
lean_object* v_res_4176_;
v_res_4176_ = l_Lean_MVarId_extractLets___lam__0(v___x_4101_, v_mvarId_4102_, v_a_4103_, v___x_4104_, v_fvarIds_4105_, v_es_4106_, v_givenNames_x27_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
stack->m_obj
 = v_res_4176_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4177_, lean_object* v_mvarId_4178_, lean_object* v_a_4179_, lean_object* v___x_4180_, lean_object* v_fvarIds_4181_, lean_object* v_es_4182_, lean_object* v_givenNames_x27_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_MVarId_extractLets___lam__0(v___x_4177_, v_mvarId_4178_, v_a_4179_, v___x_4180_, v_fvarIds_4181_, v_es_4182_, v_givenNames_x27_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec_ref(v_es_4182_);
lean_dec_ref(v_a_4179_);
lean_dec_ref(v___x_4177_);
return v_res_4189_;
}
}
lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4190_, lean_object* v___x_4191_, lean_object* v___x_4192_, lean_object* v_givenNames_4193_, lean_object* v_config_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; 
lean_inc(v___x_4191_);
lean_inc(v_mvarId_4190_);
v___x_4200_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4190_, v___x_4191_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v___x_4201_; 
lean_dec_ref_known(v___x_4200_, 1);
lean_inc(v_mvarId_4190_);
v___x_4201_ = l_Lean_MVarId_getType(v_mvarId_4190_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___f_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc_n(v_a_4202_, 2);
lean_dec_ref_known(v___x_4201_, 1);
v___f_4203_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4203_, 0, v___x_4192_);
lean_closure_set(v___f_4203_, 1, v_mvarId_4190_);
lean_closure_set(v___f_4203_, 2, v_a_4202_);
lean_closure_set(v___f_4203_, 3, v___x_4191_);
v___x_4204_ = lean_unsigned_to_nat(1u);
v___x_4205_ = lean_mk_empty_array_with_capacity(v___x_4204_);
v___x_4206_ = lean_array_push(v___x_4205_, v_a_4202_);
v___x_4207_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4206_, v_givenNames_4193_, v___f_4203_, v_config_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
return v___x_4207_;
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec(v_givenNames_4193_);
lean_dec_ref(v___x_4192_);
lean_dec(v___x_4191_);
lean_dec(v_mvarId_4190_);
v_a_4208_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4201_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4201_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_givenNames_4193_);
lean_dec_ref(v___x_4192_);
lean_dec(v___x_4191_);
lean_dec(v_mvarId_4190_);
v_a_4216_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4200_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4200_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLets___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4190_ = stack[0].m_obj;
lean_object* v___x_4191_ = stack[1].m_obj;
lean_object* v___x_4192_ = stack[2].m_obj;
lean_object* v_givenNames_4193_ = stack[3].m_obj;
lean_object* v_config_4194_ = stack[4].m_obj;
lean_object* v___y_4195_ = stack[5].m_obj;
lean_object* v___y_4196_ = stack[6].m_obj;
lean_object* v___y_4197_ = stack[7].m_obj;
lean_object* v___y_4198_ = stack[8].m_obj;
lean_object* v_res_4224_;
v_res_4224_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4190_, v___x_4191_, v___x_4192_, v_givenNames_4193_, v_config_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
stack->m_obj
 = v_res_4224_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4225_, lean_object* v___x_4226_, lean_object* v___x_4227_, lean_object* v_givenNames_4228_, lean_object* v_config_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4225_, v___x_4226_, v___x_4227_, v_givenNames_4228_, v_config_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec_ref(v_config_4229_);
return v_res_4235_;
}
}
lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4239_, lean_object* v_givenNames_4240_, lean_object* v_config_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___f_4249_; lean_object* v___x_4250_; 
v___x_4247_ = l_Lean_instInhabitedExpr;
v___x_4248_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4239_);
v___f_4249_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4249_, 0, v_mvarId_4239_);
lean_closure_set(v___f_4249_, 1, v___x_4248_);
lean_closure_set(v___f_4249_, 2, v___x_4247_);
lean_closure_set(v___f_4249_, 3, v_givenNames_4240_);
lean_closure_set(v___f_4249_, 4, v_config_4241_);
v___x_4250_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4239_, v___f_4249_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
return v___x_4250_;
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4239_ = stack[0].m_obj;
lean_object* v_givenNames_4240_ = stack[1].m_obj;
lean_object* v_config_4241_ = stack[2].m_obj;
lean_object* v_a_4242_ = stack[3].m_obj;
lean_object* v_a_4243_ = stack[4].m_obj;
lean_object* v_a_4244_ = stack[5].m_obj;
lean_object* v_a_4245_ = stack[6].m_obj;
lean_object* v_res_4251_;
v_res_4251_ = l_Lean_MVarId_extractLets(v_mvarId_4239_, v_givenNames_4240_, v_config_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
stack->m_obj
 = v_res_4251_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4252_, lean_object* v_givenNames_4253_, lean_object* v_config_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_MVarId_extractLets(v_mvarId_4252_, v_givenNames_4253_, v_config_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4257_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
return v_res_4260_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4261_, lean_object* v_val_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4261_, v_val_4262_, v___y_4264_);
return v___x_4268_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4261_ = stack[0].m_obj;
lean_object* v_val_4262_ = stack[1].m_obj;
lean_object* v___y_4263_ = stack[2].m_obj;
lean_object* v___y_4264_ = stack[3].m_obj;
lean_object* v___y_4265_ = stack[4].m_obj;
lean_object* v___y_4266_ = stack[5].m_obj;
lean_object* v_res_4269_;
v_res_4269_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4261_, v_val_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
stack->m_obj
 = v_res_4269_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4270_, lean_object* v_val_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4270_, v_val_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4279_, v_x_4280_, v_x_4281_);
return v___x_4282_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4283_, lean_object* v_x_4284_, size_t v_x_4285_, size_t v_x_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4284_, v_x_4285_, v_x_4286_, v_x_4287_, v_x_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4284_ = stack[1].m_obj;
size_t v_x_4285_ = stack[2].m_num;
size_t v_x_4286_ = stack[3].m_num;
lean_object* v_x_4287_ = stack[4].m_obj;
lean_object* v_x_4288_ = stack[5].m_obj;
lean_object* v_res_4290_;
v_res_4290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_box(0), v_x_4284_, v_x_4285_, v_x_4286_, v_x_4287_, v_x_4288_);
stack->m_obj
 = v_res_4290_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4291_, lean_object* v_x_4292_, lean_object* v_x_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_, lean_object* v_x_4296_){
_start:
{
size_t v_x_3172__boxed_4297_; size_t v_x_3173__boxed_4298_; lean_object* v_res_4299_; 
v_x_3172__boxed_4297_ = lean_unbox_usize(v_x_4293_);
lean_dec(v_x_4293_);
v_x_3173__boxed_4298_ = lean_unbox_usize(v_x_4294_);
lean_dec(v_x_4294_);
v_res_4299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4291_, v_x_4292_, v_x_3172__boxed_4297_, v_x_3173__boxed_4298_, v_x_4295_, v_x_4296_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4300_, lean_object* v_n_4301_, lean_object* v_k_4302_, lean_object* v_v_4303_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4301_, v_k_4302_, v_v_4303_);
return v___x_4304_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4305_, size_t v_depth_4306_, lean_object* v_keys_4307_, lean_object* v_vals_4308_, lean_object* v_heq_4309_, lean_object* v_i_4310_, lean_object* v_entries_4311_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4306_, v_keys_4307_, v_vals_4308_, v_i_4310_, v_entries_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_4306_ = stack[1].m_num;
lean_object* v_keys_4307_ = stack[2].m_obj;
lean_object* v_vals_4308_ = stack[3].m_obj;
lean_object* v_i_4310_ = stack[5].m_obj;
lean_object* v_entries_4311_ = stack[6].m_obj;
lean_object* v_res_4313_;
v_res_4313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_box(0), v_depth_4306_, v_keys_4307_, v_vals_4308_, lean_box(0), v_i_4310_, v_entries_4311_);
stack->m_obj
 = v_res_4313_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4314_, lean_object* v_depth_4315_, lean_object* v_keys_4316_, lean_object* v_vals_4317_, lean_object* v_heq_4318_, lean_object* v_i_4319_, lean_object* v_entries_4320_){
_start:
{
size_t v_depth_boxed_4321_; lean_object* v_res_4322_; 
v_depth_boxed_4321_ = lean_unbox_usize(v_depth_4315_);
lean_dec(v_depth_4315_);
v_res_4322_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4314_, v_depth_boxed_4321_, v_keys_4316_, v_vals_4317_, v_heq_4318_, v_i_4319_, v_entries_4320_);
lean_dec_ref(v_vals_4317_);
lean_dec_ref(v_keys_4316_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4323_, lean_object* v_x_4324_, lean_object* v_x_4325_, lean_object* v_x_4326_, lean_object* v_x_4327_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4324_, v_x_4325_, v_x_4326_, v_x_4327_);
return v___x_4328_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4329_, size_t v_i_4330_, lean_object* v_bs_4331_){
_start:
{
uint8_t v___x_4332_; 
v___x_4332_ = lean_usize_dec_lt(v_i_4330_, v_sz_4329_);
if (v___x_4332_ == 0)
{
return v_bs_4331_;
}
else
{
lean_object* v_v_4333_; lean_object* v___x_4334_; lean_object* v_bs_x27_4335_; lean_object* v___x_4336_; size_t v___x_4337_; size_t v___x_4338_; lean_object* v___x_4339_; 
v_v_4333_ = lean_array_uget(v_bs_4331_, v_i_4330_);
v___x_4334_ = lean_unsigned_to_nat(0u);
v_bs_x27_4335_ = lean_array_uset(v_bs_4331_, v_i_4330_, v___x_4334_);
v___x_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4336_, 0, v_v_4333_);
v___x_4337_ = ((size_t)1ULL);
v___x_4338_ = lean_usize_add(v_i_4330_, v___x_4337_);
v___x_4339_ = lean_array_uset(v_bs_x27_4335_, v_i_4330_, v___x_4336_);
v_i_4330_ = v___x_4338_;
v_bs_4331_ = v___x_4339_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4329_ = stack[0].m_num;
size_t v_i_4330_ = stack[1].m_num;
lean_object* v_bs_4331_ = stack[2].m_obj;
lean_object* v_res_4341_;
v_res_4341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4329_, v_i_4330_, v_bs_4331_);
stack->m_obj
 = v_res_4341_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4342_, lean_object* v_i_4343_, lean_object* v_bs_4344_){
_start:
{
size_t v_sz_boxed_4345_; size_t v_i_boxed_4346_; lean_object* v_res_4347_; 
v_sz_boxed_4345_ = lean_unbox_usize(v_sz_4342_);
lean_dec(v_sz_4342_);
v_i_boxed_4346_ = lean_unbox_usize(v_i_4343_);
lean_dec(v_i_4343_);
v_res_4347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4345_, v_i_boxed_4346_, v_bs_4344_);
return v_res_4347_;
}
}
lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4348_, lean_object* v_fvars_4349_, lean_object* v_fvarIds_4350_, lean_object* v_givenNames_x27_4351_, lean_object* v_targetNew_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v___x_4358_; 
lean_inc(v_mvarId_4348_);
v___x_4358_ = l_Lean_MVarId_getTag(v_mvarId_4348_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4352_, v_a_4359_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; size_t v_sz_4362_; size_t v___x_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; uint8_t v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc_n(v_a_4361_, 2);
lean_dec_ref_known(v___x_4360_, 1);
v_sz_4362_ = lean_array_size(v_fvarIds_4350_);
v___x_4363_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4350_);
v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4362_, v___x_4363_, v_fvarIds_4350_);
v___x_4365_ = 0;
v___x_4366_ = 1;
v___x_4367_ = 1;
v___x_4368_ = l_Lean_Meta_mkLetFVars(v___x_4364_, v_a_4361_, v___x_4365_, v___x_4366_, v___x_4367_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec_ref(v___x_4364_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4383_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
v___x_4370_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4348_, v_a_4369_, v___y_4354_);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v___x_4370_, 0);
lean_dec(v_unused_4384_);
v___x_4372_ = v___x_4370_;
v_isShared_4373_ = v_isSharedCheck_4383_;
goto v_resetjp_4371_;
}
else
{
lean_dec(v___x_4370_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4383_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4374_; size_t v_sz_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4374_, 0, v_fvarIds_4350_);
lean_ctor_set(v___x_4374_, 1, v_givenNames_x27_4351_);
v_sz_4375_ = lean_array_size(v_fvars_4349_);
v___x_4376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4375_, v___x_4363_, v_fvars_4349_);
v___x_4377_ = l_Lean_Expr_mvarId_x21(v_a_4361_);
lean_dec(v_a_4361_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4374_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4379_);
v___x_4381_ = v___x_4372_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_a_4361_);
lean_dec(v_givenNames_x27_4351_);
lean_dec_ref(v_fvarIds_4350_);
lean_dec_ref(v_fvars_4349_);
lean_dec(v_mvarId_4348_);
v_a_4385_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4368_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4368_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_givenNames_x27_4351_);
lean_dec_ref(v_fvarIds_4350_);
lean_dec_ref(v_fvars_4349_);
lean_dec(v_mvarId_4348_);
v_a_4393_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4360_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4360_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec_ref(v_targetNew_4352_);
lean_dec(v_givenNames_x27_4351_);
lean_dec_ref(v_fvarIds_4350_);
lean_dec_ref(v_fvars_4349_);
lean_dec(v_mvarId_4348_);
v_a_4401_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4358_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4358_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLetsLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4348_ = stack[0].m_obj;
lean_object* v_fvars_4349_ = stack[1].m_obj;
lean_object* v_fvarIds_4350_ = stack[2].m_obj;
lean_object* v_givenNames_x27_4351_ = stack[3].m_obj;
lean_object* v_targetNew_4352_ = stack[4].m_obj;
lean_object* v___y_4353_ = stack[5].m_obj;
lean_object* v___y_4354_ = stack[6].m_obj;
lean_object* v___y_4355_ = stack[7].m_obj;
lean_object* v___y_4356_ = stack[8].m_obj;
lean_object* v_res_4409_;
v_res_4409_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4348_, v_fvars_4349_, v_fvarIds_4350_, v_givenNames_x27_4351_, v_targetNew_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
stack->m_obj
 = v_res_4409_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4410_, lean_object* v_fvars_4411_, lean_object* v_fvarIds_4412_, lean_object* v_givenNames_x27_4413_, lean_object* v_targetNew_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4410_, v_fvars_4411_, v_fvarIds_4412_, v_givenNames_x27_4413_, v_targetNew_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
return v_res_4420_;
}
}
lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4421_, lean_object* v_binderName_4422_, lean_object* v_body_4423_, uint8_t v_binderInfo_4424_, lean_object* v___f_4425_, lean_object* v_binderType_4426_, lean_object* v___x_4427_, lean_object* v_mvarId_4428_, lean_object* v_fvarIds_4429_, lean_object* v_es_4430_, lean_object* v_givenNames_x27_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4442_; uint8_t v___x_4443_; 
v___x_4437_ = lean_unsigned_to_nat(0u);
v___x_4438_ = lean_array_get_borrowed(v___x_4421_, v_es_4430_, v___x_4437_);
v___x_4442_ = lean_array_get_size(v_fvarIds_4429_);
v___x_4443_ = lean_nat_dec_eq(v___x_4442_, v___x_4437_);
if (v___x_4443_ == 0)
{
lean_dec(v_mvarId_4428_);
lean_dec(v___x_4427_);
goto v___jp_4439_;
}
else
{
uint8_t v___x_4444_; 
v___x_4444_ = lean_expr_eqv(v_binderType_4426_, v___x_4438_);
if (v___x_4444_ == 0)
{
lean_dec(v_mvarId_4428_);
lean_dec(v___x_4427_);
goto v___jp_4439_;
}
else
{
lean_object* v___x_4445_; 
v___x_4445_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4427_, v_mvarId_4428_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_dec_ref_known(v___x_4445_, 1);
goto v___jp_4439_;
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_givenNames_x27_4431_);
lean_dec_ref(v_fvarIds_4429_);
lean_dec_ref(v___f_4425_);
lean_dec_ref(v_body_4423_);
lean_dec(v_binderName_4422_);
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
v___jp_4439_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_inc(v___x_4438_);
v___x_4440_ = l_Lean_Expr_forallE___override(v_binderName_4422_, v___x_4438_, v_body_4423_, v_binderInfo_4424_);
lean_inc(v___y_4435_);
lean_inc_ref(v___y_4434_);
lean_inc(v___y_4433_);
lean_inc_ref(v___y_4432_);
v___x_4441_ = lean_apply_8(v___f_4425_, v_fvarIds_4429_, v_givenNames_x27_4431_, v___x_4440_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, lean_box(0));
return v___x_4441_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLetsLocalDecl___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4421_ = stack[0].m_obj;
lean_object* v_binderName_4422_ = stack[1].m_obj;
lean_object* v_body_4423_ = stack[2].m_obj;
uint8_t v_binderInfo_4424_ = stack[3].m_num;
lean_object* v___f_4425_ = stack[4].m_obj;
lean_object* v_binderType_4426_ = stack[5].m_obj;
lean_object* v___x_4427_ = stack[6].m_obj;
lean_object* v_mvarId_4428_ = stack[7].m_obj;
lean_object* v_fvarIds_4429_ = stack[8].m_obj;
lean_object* v_es_4430_ = stack[9].m_obj;
lean_object* v_givenNames_x27_4431_ = stack[10].m_obj;
lean_object* v___y_4432_ = stack[11].m_obj;
lean_object* v___y_4433_ = stack[12].m_obj;
lean_object* v___y_4434_ = stack[13].m_obj;
lean_object* v___y_4435_ = stack[14].m_obj;
lean_object* v_res_4454_;
v_res_4454_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4421_, v_binderName_4422_, v_body_4423_, v_binderInfo_4424_, v___f_4425_, v_binderType_4426_, v___x_4427_, v_mvarId_4428_, v_fvarIds_4429_, v_es_4430_, v_givenNames_x27_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
stack->m_obj
 = v_res_4454_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4455_, lean_object* v_binderName_4456_, lean_object* v_body_4457_, lean_object* v_binderInfo_4458_, lean_object* v___f_4459_, lean_object* v_binderType_4460_, lean_object* v___x_4461_, lean_object* v_mvarId_4462_, lean_object* v_fvarIds_4463_, lean_object* v_es_4464_, lean_object* v_givenNames_x27_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
uint8_t v_binderInfo_1869__boxed_4471_; lean_object* v_res_4472_; 
v_binderInfo_1869__boxed_4471_ = lean_unbox(v_binderInfo_4458_);
v_res_4472_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4455_, v_binderName_4456_, v_body_4457_, v_binderInfo_1869__boxed_4471_, v___f_4459_, v_binderType_4460_, v___x_4461_, v_mvarId_4462_, v_fvarIds_4463_, v_es_4464_, v_givenNames_x27_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec_ref(v_es_4464_);
lean_dec_ref(v_binderType_4460_);
lean_dec_ref(v___x_4455_);
return v_res_4472_;
}
}
lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4473_, lean_object* v_declName_4474_, lean_object* v_body_4475_, uint8_t v_nondep_4476_, lean_object* v___f_4477_, lean_object* v_type_4478_, lean_object* v_value_4479_, lean_object* v___x_4480_, lean_object* v_mvarId_4481_, lean_object* v_fvarIds_4482_, lean_object* v_es_4483_, lean_object* v_givenNames_x27_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4497_; uint8_t v___x_4498_; 
v___x_4490_ = lean_unsigned_to_nat(0u);
v___x_4491_ = lean_array_get_borrowed(v___x_4473_, v_es_4483_, v___x_4490_);
v___x_4492_ = lean_unsigned_to_nat(1u);
v___x_4493_ = lean_array_get_borrowed(v___x_4473_, v_es_4483_, v___x_4492_);
v___x_4497_ = lean_array_get_size(v_fvarIds_4482_);
v___x_4498_ = lean_nat_dec_eq(v___x_4497_, v___x_4490_);
if (v___x_4498_ == 0)
{
lean_dec(v_mvarId_4481_);
lean_dec(v___x_4480_);
goto v___jp_4494_;
}
else
{
uint8_t v___x_4499_; 
v___x_4499_ = lean_expr_eqv(v_type_4478_, v___x_4491_);
if (v___x_4499_ == 0)
{
lean_dec(v_mvarId_4481_);
lean_dec(v___x_4480_);
goto v___jp_4494_;
}
else
{
uint8_t v___x_4500_; 
v___x_4500_ = lean_expr_eqv(v_value_4479_, v___x_4493_);
if (v___x_4500_ == 0)
{
lean_dec(v_mvarId_4481_);
lean_dec(v___x_4480_);
goto v___jp_4494_;
}
else
{
lean_object* v___x_4501_; 
v___x_4501_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4480_, v_mvarId_4481_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_dec_ref_known(v___x_4501_, 1);
goto v___jp_4494_;
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v_givenNames_x27_4484_);
lean_dec_ref(v_fvarIds_4482_);
lean_dec_ref(v___f_4477_);
lean_dec_ref(v_body_4475_);
lean_dec(v_declName_4474_);
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
}
v___jp_4494_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
lean_inc(v___x_4493_);
lean_inc(v___x_4491_);
v___x_4495_ = l_Lean_Expr_letE___override(v_declName_4474_, v___x_4491_, v___x_4493_, v_body_4475_, v_nondep_4476_);
lean_inc(v___y_4488_);
lean_inc_ref(v___y_4487_);
lean_inc(v___y_4486_);
lean_inc_ref(v___y_4485_);
v___x_4496_ = lean_apply_8(v___f_4477_, v_fvarIds_4482_, v_givenNames_x27_4484_, v___x_4495_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, lean_box(0));
return v___x_4496_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLetsLocalDecl___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4473_ = stack[0].m_obj;
lean_object* v_declName_4474_ = stack[1].m_obj;
lean_object* v_body_4475_ = stack[2].m_obj;
uint8_t v_nondep_4476_ = stack[3].m_num;
lean_object* v___f_4477_ = stack[4].m_obj;
lean_object* v_type_4478_ = stack[5].m_obj;
lean_object* v_value_4479_ = stack[6].m_obj;
lean_object* v___x_4480_ = stack[7].m_obj;
lean_object* v_mvarId_4481_ = stack[8].m_obj;
lean_object* v_fvarIds_4482_ = stack[9].m_obj;
lean_object* v_es_4483_ = stack[10].m_obj;
lean_object* v_givenNames_x27_4484_ = stack[11].m_obj;
lean_object* v___y_4485_ = stack[12].m_obj;
lean_object* v___y_4486_ = stack[13].m_obj;
lean_object* v___y_4487_ = stack[14].m_obj;
lean_object* v___y_4488_ = stack[15].m_obj;
lean_object* v_res_4510_;
v_res_4510_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4473_, v_declName_4474_, v_body_4475_, v_nondep_4476_, v___f_4477_, v_type_4478_, v_value_4479_, v___x_4480_, v_mvarId_4481_, v_fvarIds_4482_, v_es_4483_, v_givenNames_x27_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
stack->m_obj
 = v_res_4510_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4511_ = _args[0];
lean_object* v_declName_4512_ = _args[1];
lean_object* v_body_4513_ = _args[2];
lean_object* v_nondep_4514_ = _args[3];
lean_object* v___f_4515_ = _args[4];
lean_object* v_type_4516_ = _args[5];
lean_object* v_value_4517_ = _args[6];
lean_object* v___x_4518_ = _args[7];
lean_object* v_mvarId_4519_ = _args[8];
lean_object* v_fvarIds_4520_ = _args[9];
lean_object* v_es_4521_ = _args[10];
lean_object* v_givenNames_x27_4522_ = _args[11];
lean_object* v___y_4523_ = _args[12];
lean_object* v___y_4524_ = _args[13];
lean_object* v___y_4525_ = _args[14];
lean_object* v___y_4526_ = _args[15];
lean_object* v___y_4527_ = _args[16];
_start:
{
uint8_t v_nondep_1981__boxed_4528_; lean_object* v_res_4529_; 
v_nondep_1981__boxed_4528_ = lean_unbox(v_nondep_4514_);
v_res_4529_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4511_, v_declName_4512_, v_body_4513_, v_nondep_1981__boxed_4528_, v___f_4515_, v_type_4516_, v_value_4517_, v___x_4518_, v_mvarId_4519_, v_fvarIds_4520_, v_es_4521_, v_givenNames_x27_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec_ref(v_es_4521_);
lean_dec_ref(v_value_4517_);
lean_dec_ref(v_type_4516_);
lean_dec_ref(v___x_4511_);
return v_res_4529_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4534_ = l_Lean_MessageData_ofFormat(v___x_4533_);
return v___x_4534_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
}
lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4537_, lean_object* v___x_4538_, lean_object* v___f_4539_, lean_object* v___x_4540_, lean_object* v_givenNames_4541_, lean_object* v_config_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v___x_4548_; 
lean_inc(v_mvarId_4537_);
v___x_4548_ = l_Lean_MVarId_getType(v_mvarId_4537_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4549_);
lean_dec_ref_known(v___x_4548_, 1);
switch(lean_obj_tag(v_a_4549_))
{
case 7:
{
lean_object* v_binderName_4550_; lean_object* v_binderType_4551_; lean_object* v_body_4552_; uint8_t v_binderInfo_4553_; lean_object* v___x_4554_; lean_object* v___f_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v_binderName_4550_ = lean_ctor_get(v_a_4549_, 0);
lean_inc(v_binderName_4550_);
v_binderType_4551_ = lean_ctor_get(v_a_4549_, 1);
lean_inc_ref_n(v_binderType_4551_, 2);
v_body_4552_ = lean_ctor_get(v_a_4549_, 2);
lean_inc_ref(v_body_4552_);
v_binderInfo_4553_ = lean_ctor_get_uint8(v_a_4549_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4549_, 3);
v___x_4554_ = lean_box(v_binderInfo_4553_);
v___f_4555_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4555_, 0, v___x_4538_);
lean_closure_set(v___f_4555_, 1, v_binderName_4550_);
lean_closure_set(v___f_4555_, 2, v_body_4552_);
lean_closure_set(v___f_4555_, 3, v___x_4554_);
lean_closure_set(v___f_4555_, 4, v___f_4539_);
lean_closure_set(v___f_4555_, 5, v_binderType_4551_);
lean_closure_set(v___f_4555_, 6, v___x_4540_);
lean_closure_set(v___f_4555_, 7, v_mvarId_4537_);
v___x_4556_ = lean_unsigned_to_nat(1u);
v___x_4557_ = lean_mk_empty_array_with_capacity(v___x_4556_);
v___x_4558_ = lean_array_push(v___x_4557_, v_binderType_4551_);
v___x_4559_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4558_, v_givenNames_4541_, v___f_4555_, v_config_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4559_;
}
case 8:
{
lean_object* v_declName_4560_; lean_object* v_type_4561_; lean_object* v_value_4562_; lean_object* v_body_4563_; uint8_t v_nondep_4564_; lean_object* v___x_4565_; lean_object* v___f_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v_declName_4560_ = lean_ctor_get(v_a_4549_, 0);
lean_inc(v_declName_4560_);
v_type_4561_ = lean_ctor_get(v_a_4549_, 1);
lean_inc_ref_n(v_type_4561_, 2);
v_value_4562_ = lean_ctor_get(v_a_4549_, 2);
lean_inc_ref_n(v_value_4562_, 2);
v_body_4563_ = lean_ctor_get(v_a_4549_, 3);
lean_inc_ref(v_body_4563_);
v_nondep_4564_ = lean_ctor_get_uint8(v_a_4549_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4549_, 4);
v___x_4565_ = lean_box(v_nondep_4564_);
v___f_4566_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4566_, 0, v___x_4538_);
lean_closure_set(v___f_4566_, 1, v_declName_4560_);
lean_closure_set(v___f_4566_, 2, v_body_4563_);
lean_closure_set(v___f_4566_, 3, v___x_4565_);
lean_closure_set(v___f_4566_, 4, v___f_4539_);
lean_closure_set(v___f_4566_, 5, v_type_4561_);
lean_closure_set(v___f_4566_, 6, v_value_4562_);
lean_closure_set(v___f_4566_, 7, v___x_4540_);
lean_closure_set(v___f_4566_, 8, v_mvarId_4537_);
v___x_4567_ = lean_unsigned_to_nat(2u);
v___x_4568_ = lean_mk_empty_array_with_capacity(v___x_4567_);
v___x_4569_ = lean_array_push(v___x_4568_, v_type_4561_);
v___x_4570_ = lean_array_push(v___x_4569_, v_value_4562_);
v___x_4571_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4570_, v_givenNames_4541_, v___f_4566_, v_config_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4571_;
}
default: 
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_dec(v_a_4549_);
lean_dec(v_givenNames_4541_);
lean_dec_ref(v___f_4539_);
lean_dec_ref(v___x_4538_);
v___x_4572_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4573_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4540_, v_mvarId_4537_, v___x_4572_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4573_;
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_dec(v_givenNames_4541_);
lean_dec(v___x_4540_);
lean_dec_ref(v___f_4539_);
lean_dec_ref(v___x_4538_);
lean_dec(v_mvarId_4537_);
v_a_4574_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4548_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4548_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLetsLocalDecl___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4537_ = stack[0].m_obj;
lean_object* v___x_4538_ = stack[1].m_obj;
lean_object* v___f_4539_ = stack[2].m_obj;
lean_object* v___x_4540_ = stack[3].m_obj;
lean_object* v_givenNames_4541_ = stack[4].m_obj;
lean_object* v_config_4542_ = stack[5].m_obj;
lean_object* v___y_4543_ = stack[6].m_obj;
lean_object* v___y_4544_ = stack[7].m_obj;
lean_object* v___y_4545_ = stack[8].m_obj;
lean_object* v___y_4546_ = stack[9].m_obj;
lean_object* v_res_4582_;
v_res_4582_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4537_, v___x_4538_, v___f_4539_, v___x_4540_, v_givenNames_4541_, v_config_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
stack->m_obj
 = v_res_4582_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4583_, lean_object* v___x_4584_, lean_object* v___f_4585_, lean_object* v___x_4586_, lean_object* v_givenNames_4587_, lean_object* v_config_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4583_, v___x_4584_, v___f_4585_, v___x_4586_, v_givenNames_4587_, v_config_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec_ref(v_config_4588_);
return v_res_4594_;
}
}
lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4595_, lean_object* v___x_4596_, lean_object* v_givenNames_4597_, lean_object* v_config_4598_, lean_object* v_mvarId_4599_, lean_object* v_fvars_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v___f_4606_; lean_object* v___f_4607_; lean_object* v___x_4608_; 
lean_inc_n(v_mvarId_4599_, 2);
v___f_4606_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4606_, 0, v_mvarId_4599_);
lean_closure_set(v___f_4606_, 1, v_fvars_4600_);
v___f_4607_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4607_, 0, v_mvarId_4599_);
lean_closure_set(v___f_4607_, 1, v___x_4595_);
lean_closure_set(v___f_4607_, 2, v___f_4606_);
lean_closure_set(v___f_4607_, 3, v___x_4596_);
lean_closure_set(v___f_4607_, 4, v_givenNames_4597_);
lean_closure_set(v___f_4607_, 5, v_config_4598_);
v___x_4608_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4599_, v___f_4607_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
return v___x_4608_;
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLetsLocalDecl___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4595_ = stack[0].m_obj;
lean_object* v___x_4596_ = stack[1].m_obj;
lean_object* v_givenNames_4597_ = stack[2].m_obj;
lean_object* v_config_4598_ = stack[3].m_obj;
lean_object* v_mvarId_4599_ = stack[4].m_obj;
lean_object* v_fvars_4600_ = stack[5].m_obj;
lean_object* v___y_4601_ = stack[6].m_obj;
lean_object* v___y_4602_ = stack[7].m_obj;
lean_object* v___y_4603_ = stack[8].m_obj;
lean_object* v___y_4604_ = stack[9].m_obj;
lean_object* v_res_4609_;
v_res_4609_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4595_, v___x_4596_, v_givenNames_4597_, v_config_4598_, v_mvarId_4599_, v_fvars_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
stack->m_obj
 = v_res_4609_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4610_, lean_object* v___x_4611_, lean_object* v_givenNames_4612_, lean_object* v_config_4613_, lean_object* v_mvarId_4614_, lean_object* v_fvars_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4610_, v___x_4611_, v_givenNames_4612_, v_config_4613_, v_mvarId_4614_, v_fvars_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
return v_res_4621_;
}
}
lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4622_, lean_object* v_fvarId_4623_, lean_object* v_givenNames_4624_, lean_object* v_config_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___f_4633_; lean_object* v___x_4634_; 
v___x_4631_ = l_Lean_instInhabitedExpr;
v___x_4632_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
v___f_4633_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4633_, 0, v___x_4631_);
lean_closure_set(v___f_4633_, 1, v___x_4632_);
lean_closure_set(v___f_4633_, 2, v_givenNames_4624_);
lean_closure_set(v___f_4633_, 3, v_config_4625_);
lean_inc(v_mvarId_4622_);
v___x_4634_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4622_, v___x_4632_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; lean_object* v___x_4639_; 
lean_dec_ref_known(v___x_4634_, 1);
v___x_4635_ = lean_unsigned_to_nat(1u);
v___x_4636_ = lean_mk_empty_array_with_capacity(v___x_4635_);
v___x_4637_ = lean_array_push(v___x_4636_, v_fvarId_4623_);
v___x_4638_ = 0;
v___x_4639_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4622_, v___x_4637_, v___f_4633_, v___x_4638_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
return v___x_4639_;
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v___f_4633_);
lean_dec(v_fvarId_4623_);
lean_dec(v_mvarId_4622_);
v_a_4640_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4634_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4634_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_extractLetsLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4622_ = stack[0].m_obj;
lean_object* v_fvarId_4623_ = stack[1].m_obj;
lean_object* v_givenNames_4624_ = stack[2].m_obj;
lean_object* v_config_4625_ = stack[3].m_obj;
lean_object* v_a_4626_ = stack[4].m_obj;
lean_object* v_a_4627_ = stack[5].m_obj;
lean_object* v_a_4628_ = stack[6].m_obj;
lean_object* v_a_4629_ = stack[7].m_obj;
lean_object* v_res_4648_;
v_res_4648_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4622_, v_fvarId_4623_, v_givenNames_4624_, v_config_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
stack->m_obj
 = v_res_4648_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4649_, lean_object* v_fvarId_4650_, lean_object* v_givenNames_4651_, lean_object* v_config_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4649_, v_fvarId_4650_, v_givenNames_4651_, v_config_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_);
lean_dec(v_a_4656_);
lean_dec_ref(v_a_4655_);
lean_dec(v_a_4654_);
lean_dec_ref(v_a_4653_);
return v_res_4658_;
}
}
lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4659_, lean_object* v___x_4660_, lean_object* v_config_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v___x_4667_; 
lean_inc(v___x_4660_);
lean_inc(v_mvarId_4659_);
v___x_4667_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4659_, v___x_4660_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v___x_4668_; 
lean_dec_ref_known(v___x_4667_, 1);
lean_inc(v_mvarId_4659_);
v___x_4668_ = l_Lean_MVarId_getType(v_mvarId_4659_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4670_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc_n(v_a_4669_, 2);
lean_dec_ref_known(v___x_4668_, 1);
v___x_4670_ = l_Lean_Meta_liftLets(v_a_4669_, v_config_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; uint8_t v___x_4672_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v___x_4672_ = lean_expr_eqv(v_a_4669_, v_a_4671_);
lean_dec(v_a_4669_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; 
lean_dec(v___x_4660_);
v___x_4673_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4659_, v_a_4671_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
return v___x_4673_;
}
else
{
lean_object* v___x_4674_; 
lean_inc(v_mvarId_4659_);
v___x_4674_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4660_, v_mvarId_4659_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v___x_4675_; 
lean_dec_ref_known(v___x_4674_, 1);
v___x_4675_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4659_, v_a_4671_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
return v___x_4675_;
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4683_; 
lean_dec(v_a_4671_);
lean_dec(v_mvarId_4659_);
v_a_4676_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4678_ = v___x_4674_;
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4674_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4676_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_dec(v_a_4669_);
lean_dec(v___x_4660_);
lean_dec(v_mvarId_4659_);
v_a_4684_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4670_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4670_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
else
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
lean_dec_ref(v_config_4661_);
lean_dec(v___x_4660_);
lean_dec(v_mvarId_4659_);
v_a_4692_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4668_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4668_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
lean_dec_ref(v_config_4661_);
lean_dec(v___x_4660_);
lean_dec(v_mvarId_4659_);
v_a_4700_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4667_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4667_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_liftLets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4659_ = stack[0].m_obj;
lean_object* v___x_4660_ = stack[1].m_obj;
lean_object* v_config_4661_ = stack[2].m_obj;
lean_object* v___y_4662_ = stack[3].m_obj;
lean_object* v___y_4663_ = stack[4].m_obj;
lean_object* v___y_4664_ = stack[5].m_obj;
lean_object* v___y_4665_ = stack[6].m_obj;
lean_object* v_res_4708_;
v_res_4708_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4659_, v___x_4660_, v_config_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
stack->m_obj
 = v_res_4708_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4709_, lean_object* v___x_4710_, lean_object* v_config_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4709_, v___x_4710_, v_config_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
return v_res_4717_;
}
}
lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4721_, lean_object* v_config_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v___x_4728_; lean_object* v___f_4729_; lean_object* v___x_4730_; 
v___x_4728_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4721_);
v___f_4729_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4729_, 0, v_mvarId_4721_);
lean_closure_set(v___f_4729_, 1, v___x_4728_);
lean_closure_set(v___f_4729_, 2, v_config_4722_);
v___x_4730_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4721_, v___f_4729_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
return v___x_4730_;
}
}
LEAN_EXPORT void l_Lean_MVarId_liftLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4721_ = stack[0].m_obj;
lean_object* v_config_4722_ = stack[1].m_obj;
lean_object* v_a_4723_ = stack[2].m_obj;
lean_object* v_a_4724_ = stack[3].m_obj;
lean_object* v_a_4725_ = stack[4].m_obj;
lean_object* v_a_4726_ = stack[5].m_obj;
lean_object* v_res_4731_;
v_res_4731_ = l_Lean_MVarId_liftLets(v_mvarId_4721_, v_config_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
stack->m_obj
 = v_res_4731_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4732_, lean_object* v_config_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l_Lean_MVarId_liftLets(v_mvarId_4732_, v_config_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
return v_res_4739_;
}
}
lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4740_, lean_object* v_fvars_4741_, lean_object* v_targetNew_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4740_, v_targetNew_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4762_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4751_ = v___x_4748_;
v_isShared_4752_ = v_isSharedCheck_4762_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4748_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4762_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4753_; size_t v_sz_4754_; size_t v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4753_ = lean_box(0);
v_sz_4754_ = lean_array_size(v_fvars_4741_);
v___x_4755_ = ((size_t)0ULL);
v___x_4756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4754_, v___x_4755_, v_fvars_4741_);
v___x_4757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
lean_ctor_set(v___x_4757_, 1, v_a_4749_);
v___x_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4753_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4758_);
v___x_4760_ = v___x_4751_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec_ref(v_fvars_4741_);
v_a_4763_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4748_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4748_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_liftLetsLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4740_ = stack[0].m_obj;
lean_object* v_fvars_4741_ = stack[1].m_obj;
lean_object* v_targetNew_4742_ = stack[2].m_obj;
lean_object* v___y_4743_ = stack[3].m_obj;
lean_object* v___y_4744_ = stack[4].m_obj;
lean_object* v___y_4745_ = stack[5].m_obj;
lean_object* v___y_4746_ = stack[6].m_obj;
lean_object* v_res_4771_;
v_res_4771_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4740_, v_fvars_4741_, v_targetNew_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_);
stack->m_obj
 = v_res_4771_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4772_, lean_object* v_fvars_4773_, lean_object* v_targetNew_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4772_, v_fvars_4773_, v_targetNew_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
return v_res_4780_;
}
}
lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4781_, lean_object* v_config_4782_, lean_object* v___f_4783_, lean_object* v___x_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v___x_4790_; 
lean_inc(v_mvarId_4781_);
v___x_4790_ = l_Lean_MVarId_getType(v_mvarId_4781_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc(v_a_4791_);
lean_dec_ref_known(v___x_4790_, 1);
switch(lean_obj_tag(v_a_4791_))
{
case 7:
{
lean_object* v_binderName_4792_; lean_object* v_binderType_4793_; lean_object* v_body_4794_; uint8_t v_binderInfo_4795_; lean_object* v___x_4796_; 
v_binderName_4792_ = lean_ctor_get(v_a_4791_, 0);
lean_inc(v_binderName_4792_);
v_binderType_4793_ = lean_ctor_get(v_a_4791_, 1);
lean_inc_ref_n(v_binderType_4793_, 2);
v_body_4794_ = lean_ctor_get(v_a_4791_, 2);
lean_inc_ref(v_body_4794_);
v_binderInfo_4795_ = lean_ctor_get_uint8(v_a_4791_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4791_, 3);
v___x_4796_ = l_Lean_Meta_liftLets(v_binderType_4793_, v_config_4782_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___y_4799_; lean_object* v___y_4800_; lean_object* v___y_4801_; lean_object* v___y_4802_; uint8_t v___x_4805_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
lean_inc(v_a_4797_);
lean_dec_ref_known(v___x_4796_, 1);
v___x_4805_ = lean_expr_eqv(v_binderType_4793_, v_a_4797_);
lean_dec_ref(v_binderType_4793_);
if (v___x_4805_ == 0)
{
lean_dec(v___x_4784_);
lean_dec(v_mvarId_4781_);
v___y_4799_ = v___y_4785_;
v___y_4800_ = v___y_4786_;
v___y_4801_ = v___y_4787_;
v___y_4802_ = v___y_4788_;
goto v___jp_4798_;
}
else
{
lean_object* v___x_4806_; 
v___x_4806_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4784_, v_mvarId_4781_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_dec_ref_known(v___x_4806_, 1);
v___y_4799_ = v___y_4785_;
v___y_4800_ = v___y_4786_;
v___y_4801_ = v___y_4787_;
v___y_4802_ = v___y_4788_;
goto v___jp_4798_;
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec(v_a_4797_);
lean_dec_ref(v_body_4794_);
lean_dec(v_binderName_4792_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec_ref(v___f_4783_);
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
v___jp_4798_:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = l_Lean_Expr_forallE___override(v_binderName_4792_, v_a_4797_, v_body_4794_, v_binderInfo_4795_);
v___x_4804_ = lean_apply_6(v___f_4783_, v___x_4803_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, lean_box(0));
return v___x_4804_;
}
}
else
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4822_; 
lean_dec_ref(v_body_4794_);
lean_dec_ref(v_binderType_4793_);
lean_dec(v_binderName_4792_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___x_4784_);
lean_dec_ref(v___f_4783_);
lean_dec(v_mvarId_4781_);
v_a_4815_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4817_ = v___x_4796_;
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4796_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4822_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
case 8:
{
lean_object* v_declName_4823_; lean_object* v_type_4824_; lean_object* v_value_4825_; lean_object* v_body_4826_; uint8_t v_nondep_4827_; lean_object* v___x_4828_; 
v_declName_4823_ = lean_ctor_get(v_a_4791_, 0);
lean_inc(v_declName_4823_);
v_type_4824_ = lean_ctor_get(v_a_4791_, 1);
lean_inc_ref_n(v_type_4824_, 2);
v_value_4825_ = lean_ctor_get(v_a_4791_, 2);
lean_inc_ref(v_value_4825_);
v_body_4826_ = lean_ctor_get(v_a_4791_, 3);
lean_inc_ref(v_body_4826_);
v_nondep_4827_ = lean_ctor_get_uint8(v_a_4791_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4791_, 4);
lean_inc_ref(v_config_4782_);
v___x_4828_ = l_Lean_Meta_liftLets(v_type_4824_, v_config_4782_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4830_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___x_4828_, 1);
lean_inc_ref(v_value_4825_);
v___x_4830_ = l_Lean_Meta_liftLets(v_value_4825_, v_config_4782_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; uint8_t v___y_4840_; uint8_t v___x_4850_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref_known(v___x_4830_, 1);
v___x_4850_ = lean_expr_eqv(v_type_4824_, v_a_4829_);
lean_dec_ref(v_type_4824_);
if (v___x_4850_ == 0)
{
lean_dec_ref(v_value_4825_);
v___y_4840_ = v___x_4850_;
goto v___jp_4839_;
}
else
{
uint8_t v___x_4851_; 
v___x_4851_ = lean_expr_eqv(v_value_4825_, v_a_4831_);
lean_dec_ref(v_value_4825_);
v___y_4840_ = v___x_4851_;
goto v___jp_4839_;
}
v___jp_4832_:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = l_Lean_Expr_letE___override(v_declName_4823_, v_a_4829_, v_a_4831_, v_body_4826_, v_nondep_4827_);
v___x_4838_ = lean_apply_6(v___f_4783_, v___x_4837_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, lean_box(0));
return v___x_4838_;
}
v___jp_4839_:
{
if (v___y_4840_ == 0)
{
lean_dec(v___x_4784_);
lean_dec(v_mvarId_4781_);
v___y_4833_ = v___y_4785_;
v___y_4834_ = v___y_4786_;
v___y_4835_ = v___y_4787_;
v___y_4836_ = v___y_4788_;
goto v___jp_4832_;
}
else
{
lean_object* v___x_4841_; 
v___x_4841_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4784_, v_mvarId_4781_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_dec_ref_known(v___x_4841_, 1);
v___y_4833_ = v___y_4785_;
v___y_4834_ = v___y_4786_;
v___y_4835_ = v___y_4787_;
v___y_4836_ = v___y_4788_;
goto v___jp_4832_;
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec(v_a_4831_);
lean_dec(v_a_4829_);
lean_dec_ref(v_body_4826_);
lean_dec(v_declName_4823_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec_ref(v___f_4783_);
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4841_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4841_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_dec(v_a_4829_);
lean_dec_ref(v_body_4826_);
lean_dec_ref(v_value_4825_);
lean_dec_ref(v_type_4824_);
lean_dec(v_declName_4823_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___x_4784_);
lean_dec_ref(v___f_4783_);
lean_dec(v_mvarId_4781_);
v_a_4852_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4830_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4830_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
lean_dec_ref(v_body_4826_);
lean_dec_ref(v_value_4825_);
lean_dec_ref(v_type_4824_);
lean_dec(v_declName_4823_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___x_4784_);
lean_dec_ref(v___f_4783_);
lean_dec_ref(v_config_4782_);
lean_dec(v_mvarId_4781_);
v_a_4860_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4828_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4828_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
default: 
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_dec(v_a_4791_);
lean_dec_ref(v___f_4783_);
lean_dec_ref(v_config_4782_);
v___x_4868_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4869_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4784_, v_mvarId_4781_, v___x_4868_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
return v___x_4869_;
}
}
}
else
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4877_; 
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___x_4784_);
lean_dec_ref(v___f_4783_);
lean_dec_ref(v_config_4782_);
lean_dec(v_mvarId_4781_);
v_a_4870_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4872_ = v___x_4790_;
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4790_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_a_4870_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_liftLetsLocalDecl___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4781_ = stack[0].m_obj;
lean_object* v_config_4782_ = stack[1].m_obj;
lean_object* v___f_4783_ = stack[2].m_obj;
lean_object* v___x_4784_ = stack[3].m_obj;
lean_object* v___y_4785_ = stack[4].m_obj;
lean_object* v___y_4786_ = stack[5].m_obj;
lean_object* v___y_4787_ = stack[6].m_obj;
lean_object* v___y_4788_ = stack[7].m_obj;
lean_object* v_res_4878_;
v_res_4878_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4781_, v_config_4782_, v___f_4783_, v___x_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
stack->m_obj
 = v_res_4878_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4879_, lean_object* v_config_4880_, lean_object* v___f_4881_, lean_object* v___x_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4879_, v_config_4880_, v___f_4881_, v___x_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
return v_res_4888_;
}
}
lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4889_, lean_object* v___x_4890_, lean_object* v_mvarId_4891_, lean_object* v_fvars_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v___f_4898_; lean_object* v___f_4899_; lean_object* v___x_4900_; 
lean_inc_n(v_mvarId_4891_, 2);
v___f_4898_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4898_, 0, v_mvarId_4891_);
lean_closure_set(v___f_4898_, 1, v_fvars_4892_);
v___f_4899_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4899_, 0, v_mvarId_4891_);
lean_closure_set(v___f_4899_, 1, v_config_4889_);
lean_closure_set(v___f_4899_, 2, v___f_4898_);
lean_closure_set(v___f_4899_, 3, v___x_4890_);
v___x_4900_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4891_, v___f_4899_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
return v___x_4900_;
}
}
LEAN_EXPORT void l_Lean_MVarId_liftLetsLocalDecl___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_4889_ = stack[0].m_obj;
lean_object* v___x_4890_ = stack[1].m_obj;
lean_object* v_mvarId_4891_ = stack[2].m_obj;
lean_object* v_fvars_4892_ = stack[3].m_obj;
lean_object* v___y_4893_ = stack[4].m_obj;
lean_object* v___y_4894_ = stack[5].m_obj;
lean_object* v___y_4895_ = stack[6].m_obj;
lean_object* v___y_4896_ = stack[7].m_obj;
lean_object* v_res_4901_;
v_res_4901_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4889_, v___x_4890_, v_mvarId_4891_, v_fvars_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
stack->m_obj
 = v_res_4901_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4902_, lean_object* v___x_4903_, lean_object* v_mvarId_4904_, lean_object* v_fvars_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4902_, v___x_4903_, v_mvarId_4904_, v_fvars_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
return v_res_4911_;
}
}
lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4912_, lean_object* v_fvarId_4913_, lean_object* v_config_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_){
_start:
{
lean_object* v___x_4920_; lean_object* v___f_4921_; lean_object* v___x_4922_; 
v___x_4920_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
v___f_4921_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4921_, 0, v_config_4914_);
lean_closure_set(v___f_4921_, 1, v___x_4920_);
lean_inc(v_mvarId_4912_);
v___x_4922_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4912_, v___x_4920_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; lean_object* v___x_4927_; 
lean_dec_ref_known(v___x_4922_, 1);
v___x_4923_ = lean_unsigned_to_nat(1u);
v___x_4924_ = lean_mk_empty_array_with_capacity(v___x_4923_);
v___x_4925_ = lean_array_push(v___x_4924_, v_fvarId_4913_);
v___x_4926_ = 0;
v___x_4927_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4912_, v___x_4925_, v___f_4921_, v___x_4926_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4936_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4936_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4936_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v_snd_4932_; lean_object* v___x_4934_; 
v_snd_4932_ = lean_ctor_get(v_a_4928_, 1);
lean_inc(v_snd_4932_);
lean_dec(v_a_4928_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v_snd_4932_);
v___x_4934_ = v___x_4930_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_snd_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
v_a_4937_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4927_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4927_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4940_ == 0)
{
v___x_4942_ = v___x_4939_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
else
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4952_; 
lean_dec_ref(v___f_4921_);
lean_dec(v_fvarId_4913_);
lean_dec(v_mvarId_4912_);
v_a_4945_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___x_4922_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4922_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4950_; 
if (v_isShared_4948_ == 0)
{
v___x_4950_ = v___x_4947_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_liftLetsLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4912_ = stack[0].m_obj;
lean_object* v_fvarId_4913_ = stack[1].m_obj;
lean_object* v_config_4914_ = stack[2].m_obj;
lean_object* v_a_4915_ = stack[3].m_obj;
lean_object* v_a_4916_ = stack[4].m_obj;
lean_object* v_a_4917_ = stack[5].m_obj;
lean_object* v_a_4918_ = stack[6].m_obj;
lean_object* v_res_4953_;
v_res_4953_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4912_, v_fvarId_4913_, v_config_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
stack->m_obj
 = v_res_4953_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4954_, lean_object* v_fvarId_4955_, lean_object* v_config_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4954_, v_fvarId_4955_, v_config_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
return v_res_4962_;
}
}
lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4963_, lean_object* v___x_4964_, uint8_t v_failIfUnchanged_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v___x_4971_; 
lean_inc(v___x_4964_);
lean_inc(v_mvarId_4963_);
v___x_4971_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4963_, v___x_4964_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v___x_4972_; 
lean_dec_ref_known(v___x_4971_, 1);
lean_inc(v_mvarId_4963_);
v___x_4972_ = l_Lean_MVarId_getType(v_mvarId_4963_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v___x_4974_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
lean_inc_n(v_a_4973_, 2);
lean_dec_ref_known(v___x_4972_, 1);
v___x_4974_ = l_Lean_Meta_letToHave(v_a_4973_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_4974_) == 0)
{
if (v_failIfUnchanged_4965_ == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4976_; 
lean_dec(v_a_4973_);
lean_dec(v___x_4964_);
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4974_, 1);
v___x_4976_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4963_, v_a_4975_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
return v___x_4976_;
}
else
{
lean_object* v_a_4977_; uint8_t v___x_4978_; 
v_a_4977_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4974_, 1);
v___x_4978_ = lean_expr_eqv(v_a_4973_, v_a_4977_);
lean_dec(v_a_4973_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; 
lean_dec(v___x_4964_);
v___x_4979_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4963_, v_a_4977_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
return v___x_4979_;
}
else
{
lean_object* v___x_4980_; 
lean_inc(v_mvarId_4963_);
v___x_4980_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4964_, v_mvarId_4963_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v___x_4981_; 
lean_dec_ref_known(v___x_4980_, 1);
v___x_4981_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4963_, v_a_4977_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
return v___x_4981_;
}
else
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4989_; 
lean_dec(v_a_4977_);
lean_dec(v_mvarId_4963_);
v_a_4982_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4984_ = v___x_4980_;
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4980_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4987_; 
if (v_isShared_4985_ == 0)
{
v___x_4987_ = v___x_4984_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_dec(v_a_4973_);
lean_dec(v___x_4964_);
lean_dec(v_mvarId_4963_);
v_a_4990_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4974_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4974_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec(v___x_4964_);
lean_dec(v_mvarId_4963_);
v_a_4998_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4972_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4972_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_dec(v___x_4964_);
lean_dec(v_mvarId_4963_);
v_a_5006_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4971_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4971_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_letToHave___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4963_ = stack[0].m_obj;
lean_object* v___x_4964_ = stack[1].m_obj;
uint8_t v_failIfUnchanged_4965_ = stack[2].m_num;
lean_object* v___y_4966_ = stack[3].m_obj;
lean_object* v___y_4967_ = stack[4].m_obj;
lean_object* v___y_4968_ = stack[5].m_obj;
lean_object* v___y_4969_ = stack[6].m_obj;
lean_object* v_res_5014_;
v_res_5014_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4963_, v___x_4964_, v_failIfUnchanged_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
stack->m_obj
 = v_res_5014_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_5015_, lean_object* v___x_5016_, lean_object* v_failIfUnchanged_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5023_; lean_object* v_res_5024_; 
v_failIfUnchanged_boxed_5023_ = lean_unbox(v_failIfUnchanged_5017_);
v_res_5024_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_5015_, v___x_5016_, v_failIfUnchanged_boxed_5023_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
return v_res_5024_;
}
}
lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_5028_, uint8_t v_failIfUnchanged_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___f_5037_; lean_object* v___x_5038_; 
v___x_5035_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5036_ = lean_box(v_failIfUnchanged_5029_);
lean_inc(v_mvarId_5028_);
v___f_5037_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5037_, 0, v_mvarId_5028_);
lean_closure_set(v___f_5037_, 1, v___x_5035_);
lean_closure_set(v___f_5037_, 2, v___x_5036_);
v___x_5038_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5028_, v___f_5037_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
return v___x_5038_;
}
}
LEAN_EXPORT void l_Lean_MVarId_letToHave_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5028_ = stack[0].m_obj;
uint8_t v_failIfUnchanged_5029_ = stack[1].m_num;
lean_object* v_a_5030_ = stack[2].m_obj;
lean_object* v_a_5031_ = stack[3].m_obj;
lean_object* v_a_5032_ = stack[4].m_obj;
lean_object* v_a_5033_ = stack[5].m_obj;
lean_object* v_res_5039_;
v_res_5039_ = l_Lean_MVarId_letToHave(v_mvarId_5028_, v_failIfUnchanged_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
stack->m_obj
 = v_res_5039_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_5040_, lean_object* v_failIfUnchanged_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5047_; lean_object* v_res_5048_; 
v_failIfUnchanged_boxed_5047_ = lean_unbox(v_failIfUnchanged_5041_);
v_res_5048_ = l_Lean_MVarId_letToHave(v_mvarId_5040_, v_failIfUnchanged_boxed_5047_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
return v_res_5048_;
}
}
lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_5049_, lean_object* v___x_5050_, lean_object* v_fvarId_5051_, uint8_t v_failIfUnchanged_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v___x_5058_; 
lean_inc(v___x_5050_);
lean_inc(v_mvarId_5049_);
v___x_5058_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_5049_, v___x_5050_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v___x_5059_; 
lean_dec_ref_known(v___x_5058_, 1);
lean_inc(v_fvarId_5051_);
v___x_5059_ = l_Lean_FVarId_getType___redArg(v_fvarId_5051_, v___y_5053_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; lean_object* v___x_5061_; 
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
lean_inc_n(v_a_5060_, 2);
lean_dec_ref_known(v___x_5059_, 1);
v___x_5061_ = l_Lean_Meta_letToHave(v_a_5060_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5061_) == 0)
{
if (v_failIfUnchanged_5052_ == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5063_; 
lean_dec(v_a_5060_);
lean_dec(v___x_5050_);
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
lean_inc(v_a_5062_);
lean_dec_ref_known(v___x_5061_, 1);
v___x_5063_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5049_, v_fvarId_5051_, v_a_5062_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
return v___x_5063_;
}
else
{
lean_object* v_a_5064_; uint8_t v___x_5065_; 
v_a_5064_ = lean_ctor_get(v___x_5061_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5061_, 1);
v___x_5065_ = lean_expr_eqv(v_a_5060_, v_a_5064_);
lean_dec(v_a_5060_);
if (v___x_5065_ == 0)
{
lean_object* v___x_5066_; 
lean_dec(v___x_5050_);
v___x_5066_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5049_, v_fvarId_5051_, v_a_5064_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; 
lean_inc(v_mvarId_5049_);
v___x_5067_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_5050_, v_mvarId_5049_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v___x_5068_; 
lean_dec_ref_known(v___x_5067_, 1);
v___x_5068_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5049_, v_fvarId_5051_, v_a_5064_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
return v___x_5068_;
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_dec(v_a_5064_);
lean_dec(v_fvarId_5051_);
lean_dec(v_mvarId_5049_);
v_a_5069_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5067_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5067_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_dec(v_a_5060_);
lean_dec(v_fvarId_5051_);
lean_dec(v___x_5050_);
lean_dec(v_mvarId_5049_);
v_a_5077_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5061_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5061_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec(v_fvarId_5051_);
lean_dec(v___x_5050_);
lean_dec(v_mvarId_5049_);
v_a_5085_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5059_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5059_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec(v_fvarId_5051_);
lean_dec(v___x_5050_);
lean_dec(v_mvarId_5049_);
v_a_5093_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5058_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5058_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_letToHaveLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5049_ = stack[0].m_obj;
lean_object* v___x_5050_ = stack[1].m_obj;
lean_object* v_fvarId_5051_ = stack[2].m_obj;
uint8_t v_failIfUnchanged_5052_ = stack[3].m_num;
lean_object* v___y_5053_ = stack[4].m_obj;
lean_object* v___y_5054_ = stack[5].m_obj;
lean_object* v___y_5055_ = stack[6].m_obj;
lean_object* v___y_5056_ = stack[7].m_obj;
lean_object* v_res_5101_;
v_res_5101_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5049_, v___x_5050_, v_fvarId_5051_, v_failIfUnchanged_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
stack->m_obj
 = v_res_5101_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5102_, lean_object* v___x_5103_, lean_object* v_fvarId_5104_, lean_object* v_failIfUnchanged_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5111_; lean_object* v_res_5112_; 
v_failIfUnchanged_boxed_5111_ = lean_unbox(v_failIfUnchanged_5105_);
v_res_5112_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5102_, v___x_5103_, v_fvarId_5104_, v_failIfUnchanged_boxed_5111_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
lean_dec(v___y_5109_);
lean_dec_ref(v___y_5108_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
return v_res_5112_;
}
}
lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5113_, lean_object* v_fvarId_5114_, uint8_t v_failIfUnchanged_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___f_5123_; lean_object* v___x_5124_; 
v___x_5121_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5122_ = lean_box(v_failIfUnchanged_5115_);
lean_inc(v_mvarId_5113_);
v___f_5123_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5123_, 0, v_mvarId_5113_);
lean_closure_set(v___f_5123_, 1, v___x_5121_);
lean_closure_set(v___f_5123_, 2, v_fvarId_5114_);
lean_closure_set(v___f_5123_, 3, v___x_5122_);
v___x_5124_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5113_, v___f_5123_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_);
return v___x_5124_;
}
}
LEAN_EXPORT void l_Lean_MVarId_letToHaveLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5113_ = stack[0].m_obj;
lean_object* v_fvarId_5114_ = stack[1].m_obj;
uint8_t v_failIfUnchanged_5115_ = stack[2].m_num;
lean_object* v_a_5116_ = stack[3].m_obj;
lean_object* v_a_5117_ = stack[4].m_obj;
lean_object* v_a_5118_ = stack[5].m_obj;
lean_object* v_a_5119_ = stack[6].m_obj;
lean_object* v_res_5125_;
v_res_5125_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5113_, v_fvarId_5114_, v_failIfUnchanged_5115_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_);
stack->m_obj
 = v_res_5125_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5126_, lean_object* v_fvarId_5127_, lean_object* v_failIfUnchanged_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5134_; lean_object* v_res_5135_; 
v_failIfUnchanged_boxed_5134_ = lean_unbox(v_failIfUnchanged_5128_);
v_res_5135_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5126_, v_fvarId_5127_, v_failIfUnchanged_boxed_5134_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
lean_dec(v_a_5130_);
lean_dec_ref(v_a_5129_);
return v_res_5135_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LetToHave(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_ExtractLets_instInhabitedState_default = _init_l_Lean_Meta_ExtractLets_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_ExtractLets_instInhabitedState_default);
l_Lean_Meta_ExtractLets_instInhabitedState = _init_l_Lean_Meta_ExtractLets_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_ExtractLets_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_LetToHave(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Lets(builtin);
}
#ifdef __cplusplus
}
#endif
