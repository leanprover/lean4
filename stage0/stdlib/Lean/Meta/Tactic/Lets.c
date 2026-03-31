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
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
static const lean_array_object l_Lean_Meta_ExtractLets_flushDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_ExtractLets_flushDecls___closed__0 = (const lean_object*)&l_Lean_Meta_ExtractLets_flushDecls___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ExtractLets_flushDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_ExtractLets_flushDecls___closed__0_value),((lean_object*)&l_Lean_Meta_ExtractLets_flushDecls___closed__0_value)}};
static const lean_object* l_Lean_Meta_ExtractLets_flushDecls___closed__1 = (const lean_object*)&l_Lean_Meta_ExtractLets_flushDecls___closed__1_value;
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
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg(lean_object* v_a_15_, lean_object* v_a_16_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg___boxed(lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_30_, v_a_31_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName(lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_34_, v_a_36_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___boxed(lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_ExtractLets_hasNextName(v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg(lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_givenNames_61_; 
v___x_60_ = lean_st_ref_get(v_a_58_);
v_givenNames_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_givenNames_61_);
if (lean_obj_tag(v_givenNames_61_) == 0)
{
uint8_t v_onlyGivenNames_62_; 
lean_dec(v___x_60_);
v_onlyGivenNames_62_ = lean_ctor_get_uint8(v_a_57_, 8);
if (v_onlyGivenNames_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2));
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
else
{
lean_object* v_decls_67_; lean_object* v_valueMap_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_80_; 
v_decls_67_ = lean_ctor_get(v___x_60_, 1);
v_valueMap_68_ = lean_ctor_get(v___x_60_, 2);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_60_, 0);
lean_dec(v_unused_81_);
v___x_70_ = v___x_60_;
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_valueMap_68_);
lean_inc(v_decls_67_);
lean_dec(v___x_60_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_head_72_; lean_object* v_tail_73_; lean_object* v___x_75_; 
v_head_72_ = lean_ctor_get(v_givenNames_61_, 0);
lean_inc(v_head_72_);
v_tail_73_ = lean_ctor_get(v_givenNames_61_, 1);
lean_inc(v_tail_73_);
lean_dec_ref(v_givenNames_61_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v_tail_73_);
v___x_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_tail_73_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_decls_67_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_valueMap_68_);
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_st_ref_set(v_a_58_, v___x_75_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v_head_72_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___boxed(lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f(lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_86_, v_a_88_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___boxed(lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_ExtractLets_nextName_x3f(v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(lean_object* v_binderName_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; lean_object* v_a_114_; 
v___x_113_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_108_, v_a_109_);
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
if (lean_obj_tag(v_a_114_) == 1)
{
lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_165_; 
v_val_115_ = lean_ctor_get(v_a_114_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_165_ == 0)
{
v___x_117_ = v_a_114_;
v_isShared_118_ = v_isSharedCheck_165_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_dec(v_a_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_165_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1));
v___x_120_ = lean_name_eq(v_val_115_, v___x_119_);
if (v___x_120_ == 0)
{
lean_del_object(v___x_117_);
lean_dec(v_val_115_);
lean_dec(v_binderName_107_);
return v___x_113_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = l_Lean_Name_isAnonymous(v_binderName_107_);
if (v___x_121_ == 0)
{
uint8_t v_preserveBinderNames_122_; 
v_preserveBinderNames_122_ = lean_ctor_get_uint8(v_a_108_, 9);
if (v_preserveBinderNames_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_Name_hasMacroScopes(v_val_115_);
lean_dec(v_val_115_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref(v___x_113_);
v___x_124_ = l_Lean_Core_mkFreshUserName(v_binderName_107_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_a_125_);
v___x_130_ = v___x_117_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_130_);
v___x_132_ = v___x_127_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
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
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_del_object(v___x_117_);
v_a_136_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_124_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_124_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
else
{
lean_del_object(v___x_117_);
lean_dec(v_binderName_107_);
return v___x_113_;
}
}
else
{
lean_del_object(v___x_117_);
lean_dec(v_val_115_);
lean_dec(v_binderName_107_);
return v___x_113_;
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_val_115_);
lean_dec_ref(v___x_113_);
lean_dec(v_binderName_107_);
v___x_144_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1));
v___x_145_ = l_Lean_Core_mkFreshUserName(v___x_144_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_156_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_156_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_156_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_156_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_a_146_);
v___x_151_ = v___x_117_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_155_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_151_);
v___x_153_ = v___x_148_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_del_object(v___x_117_);
v_a_157_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_145_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_145_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
lean_dec(v_a_114_);
lean_dec(v_binderName_107_);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v___x_113_, 0);
lean_dec(v_unused_174_);
v___x_167_ = v___x_113_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_dec(v___x_113_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___boxed(lean_object* v_binderName_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(lean_object* v_binderName_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_182_, v_a_183_, v_a_185_, v_a_188_, v_a_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___boxed(lean_object* v_binderName_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(v_binderName_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
return v_res_201_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
else
{
lean_object* v_head_205_; lean_object* v_tail_206_; uint8_t v___x_207_; 
v_head_205_ = lean_ctor_get(v_x_203_, 0);
v_tail_206_ = lean_ctor_get(v_x_203_, 1);
v___x_207_ = lean_expr_eqv(v_a_202_, v_head_205_);
if (v___x_207_ == 0)
{
v_x_203_ = v_tail_206_;
goto _start;
}
else
{
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0___boxed(lean_object* v_a_209_, lean_object* v_x_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v_a_209_, v_x_210_);
lean_dec(v_x_210_);
lean_dec_ref(v_a_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(lean_object* v_fvars_213_, lean_object* v_e_214_){
_start:
{
uint8_t v___x_215_; lean_object* v_d_217_; lean_object* v_b_218_; 
v___x_215_ = l_Lean_Expr_hasFVar(v_e_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v_e_214_);
return v___x_215_;
}
else
{
switch(lean_obj_tag(v_e_214_))
{
case 7:
{
lean_object* v_binderType_221_; lean_object* v_body_222_; 
v_binderType_221_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_binderType_221_);
v_body_222_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_body_222_);
lean_dec_ref(v_e_214_);
v_d_217_ = v_binderType_221_;
v_b_218_ = v_body_222_;
goto v___jp_216_;
}
case 6:
{
lean_object* v_binderType_223_; lean_object* v_body_224_; 
v_binderType_223_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_binderType_223_);
v_body_224_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_body_224_);
lean_dec_ref(v_e_214_);
v_d_217_ = v_binderType_223_;
v_b_218_ = v_body_224_;
goto v___jp_216_;
}
case 10:
{
lean_object* v_expr_225_; 
v_expr_225_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_expr_225_);
lean_dec_ref(v_e_214_);
v_e_214_ = v_expr_225_;
goto _start;
}
case 8:
{
lean_object* v_type_227_; lean_object* v_value_228_; lean_object* v_body_229_; uint8_t v___x_230_; 
v_type_227_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_type_227_);
v_value_228_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_value_228_);
v_body_229_ = lean_ctor_get(v_e_214_, 3);
lean_inc_ref(v_body_229_);
lean_dec_ref(v_e_214_);
v___x_230_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_213_, v_type_227_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
v___x_231_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_213_, v_value_228_);
if (v___x_231_ == 0)
{
v_e_214_ = v_body_229_;
goto _start;
}
else
{
lean_dec_ref(v_body_229_);
return v___x_215_;
}
}
else
{
lean_dec_ref(v_body_229_);
lean_dec_ref(v_value_228_);
return v___x_215_;
}
}
case 5:
{
lean_object* v_fn_233_; lean_object* v_arg_234_; uint8_t v___x_235_; 
v_fn_233_ = lean_ctor_get(v_e_214_, 0);
lean_inc_ref(v_fn_233_);
v_arg_234_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_arg_234_);
lean_dec_ref(v_e_214_);
v___x_235_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_213_, v_fn_233_);
if (v___x_235_ == 0)
{
v_e_214_ = v_arg_234_;
goto _start;
}
else
{
lean_dec_ref(v_arg_234_);
return v___x_215_;
}
}
case 11:
{
lean_object* v_struct_237_; 
v_struct_237_ = lean_ctor_get(v_e_214_, 2);
lean_inc_ref(v_struct_237_);
lean_dec_ref(v_e_214_);
v_e_214_ = v_struct_237_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_fvarId_239_ = lean_ctor_get(v_e_214_, 0);
lean_inc(v_fvarId_239_);
lean_dec_ref(v_e_214_);
v___x_240_ = l_Lean_Expr_fvar___override(v_fvarId_239_);
v___x_241_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v___x_240_, v_fvars_213_);
lean_dec_ref(v___x_240_);
return v___x_241_;
}
default: 
{
uint8_t v___x_242_; 
lean_dec_ref(v_e_214_);
v___x_242_ = 0;
return v___x_242_;
}
}
}
v___jp_216_:
{
uint8_t v___x_219_; 
v___x_219_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_213_, v_d_217_);
if (v___x_219_ == 0)
{
v_e_214_ = v_b_218_;
goto _start;
}
else
{
lean_dec_ref(v_b_218_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1___boxed(lean_object* v_fvars_243_, lean_object* v_e_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_243_, v_e_244_);
lean_dec(v_fvars_243_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_extractable(lean_object* v_fvars_247_, lean_object* v_e_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_247_, v_e_248_);
if (v___x_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 1;
return v___x_250_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractable___boxed(lean_object* v_fvars_252_, lean_object* v_e_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_252_, v_e_253_);
lean_dec(v_fvars_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg(lean_object* v_fvars_256_, lean_object* v_n_257_, lean_object* v_t_258_, lean_object* v_v_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___y_266_; lean_object* v___x_271_; lean_object* v_a_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_260_, v_a_261_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_271_);
v___x_273_ = lean_unbox(v_a_272_);
lean_dec(v_a_272_);
if (v___x_273_ == 0)
{
lean_dec_ref(v_v_259_);
lean_dec_ref(v_t_258_);
v___y_266_ = v_a_260_;
goto v___jp_265_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_256_, v_t_258_);
if (v___x_274_ == 0)
{
lean_dec_ref(v_v_259_);
v___y_266_ = v_a_260_;
goto v___jp_265_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_256_, v_v_259_);
if (v___x_275_ == 0)
{
v___y_266_ = v_a_260_;
goto v___jp_265_;
}
else
{
lean_object* v___x_276_; 
lean_inc(v_n_257_);
v___x_276_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_n_257_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_287_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_287_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
if (lean_obj_tag(v_a_277_) == 1)
{
lean_object* v_val_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
lean_dec(v_n_257_);
v_val_281_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_val_281_);
lean_dec_ref(v_a_277_);
v___x_282_ = lean_box(v___x_274_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_val_281_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_283_);
v___x_285_ = v___x_279_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
else
{
lean_del_object(v___x_279_);
lean_dec(v_a_277_);
v___y_266_ = v_a_260_;
goto v___jp_265_;
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_n_257_);
v_a_288_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_276_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_276_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
}
v___jp_265_:
{
uint8_t v_lift_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_lift_267_ = lean_ctor_get_uint8(v___y_266_, 10);
v___x_268_ = lean_box(v_lift_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_n_257_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg___boxed(lean_object* v_fvars_296_, lean_object* v_n_297_, lean_object* v_t_298_, lean_object* v_v_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_296_, v_n_297_, v_t_298_, v_v_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_fvars_296_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet(lean_object* v_fvars_306_, lean_object* v_n_307_, lean_object* v_t_308_, lean_object* v_v_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_306_, v_n_307_, v_t_308_, v_v_309_, v_a_310_, v_a_312_, v_a_315_, v_a_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___boxed(lean_object* v_fvars_319_, lean_object* v_n_320_, lean_object* v_t_321_, lean_object* v_v_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_ExtractLets_isExtractableLet(v_fvars_319_, v_n_320_, v_t_321_, v_v_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_fvars_319_);
return v_res_331_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
uint8_t v___x_334_; 
v___x_334_ = 0;
return v___x_334_;
}
else
{
lean_object* v_key_335_; lean_object* v_tail_336_; uint8_t v___x_337_; 
v_key_335_ = lean_ctor_get(v_x_333_, 0);
v_tail_336_ = lean_ctor_get(v_x_333_, 2);
v___x_337_ = l_Lean_ExprStructEq_beq(v_key_335_, v_a_332_);
if (v___x_337_ == 0)
{
v_x_333_ = v_tail_336_;
goto _start;
}
else
{
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_339_, lean_object* v_x_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_339_, v_x_340_);
lean_dec(v_x_340_);
lean_dec_ref(v_a_339_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_dec(v_b_344_);
lean_dec_ref(v_a_343_);
return v_x_345_;
}
else
{
lean_object* v_key_346_; lean_object* v_value_347_; lean_object* v_tail_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_360_; 
v_key_346_ = lean_ctor_get(v_x_345_, 0);
v_value_347_ = lean_ctor_get(v_x_345_, 1);
v_tail_348_ = lean_ctor_get(v_x_345_, 2);
v_isSharedCheck_360_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_360_ == 0)
{
v___x_350_ = v_x_345_;
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_tail_348_);
lean_inc(v_value_347_);
lean_inc(v_key_346_);
lean_dec(v_x_345_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___x_352_; 
v___x_352_ = l_Lean_ExprStructEq_beq(v_key_346_, v_a_343_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_343_, v_b_344_, v_tail_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 2, v___x_353_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_key_346_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_value_347_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v_value_347_);
lean_dec(v_key_346_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v_b_344_);
lean_ctor_set(v___x_350_, 0, v_a_343_);
v___x_358_ = v___x_350_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_343_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_b_344_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_tail_348_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
return v_x_361_;
}
else
{
lean_object* v_key_363_; lean_object* v_value_364_; lean_object* v_tail_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_388_; 
v_key_363_ = lean_ctor_get(v_x_362_, 0);
v_value_364_ = lean_ctor_get(v_x_362_, 1);
v_tail_365_ = lean_ctor_get(v_x_362_, 2);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_388_ == 0)
{
v___x_367_ = v_x_362_;
v_isShared_368_ = v_isSharedCheck_388_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_tail_365_);
lean_inc(v_value_364_);
lean_inc(v_key_363_);
lean_dec(v_x_362_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_388_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v_fold_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_369_ = lean_array_get_size(v_x_361_);
v___x_370_ = l_Lean_ExprStructEq_hash(v_key_363_);
v___x_371_ = 32ULL;
v___x_372_ = lean_uint64_shift_right(v___x_370_, v___x_371_);
v_fold_373_ = lean_uint64_xor(v___x_370_, v___x_372_);
v___x_374_ = 16ULL;
v___x_375_ = lean_uint64_shift_right(v_fold_373_, v___x_374_);
v___x_376_ = lean_uint64_xor(v_fold_373_, v___x_375_);
v___x_377_ = lean_uint64_to_usize(v___x_376_);
v___x_378_ = lean_usize_of_nat(v___x_369_);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_sub(v___x_378_, v___x_379_);
v___x_381_ = lean_usize_land(v___x_377_, v___x_380_);
v___x_382_ = lean_array_uget_borrowed(v_x_361_, v___x_381_);
lean_inc(v___x_382_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 2, v___x_382_);
v___x_384_ = v___x_367_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_key_363_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_value_364_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v___x_382_);
v___x_384_ = v_reuseFailAlloc_387_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; 
v___x_385_ = lean_array_uset(v_x_361_, v___x_381_, v___x_384_);
v_x_361_ = v___x_385_;
v_x_362_ = v_tail_365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(lean_object* v_i_389_, lean_object* v_source_390_, lean_object* v_target_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_array_get_size(v_source_390_);
v___x_393_ = lean_nat_dec_lt(v_i_389_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec_ref(v_source_390_);
lean_dec(v_i_389_);
return v_target_391_;
}
else
{
lean_object* v_es_394_; lean_object* v___x_395_; lean_object* v_source_396_; lean_object* v_target_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_es_394_ = lean_array_fget(v_source_390_, v_i_389_);
v___x_395_ = lean_box(0);
v_source_396_ = lean_array_fset(v_source_390_, v_i_389_, v___x_395_);
v_target_397_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(v_target_391_, v_es_394_);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_i_389_, v___x_398_);
lean_dec(v_i_389_);
v_i_389_ = v___x_399_;
v_source_390_ = v_source_396_;
v_target_391_ = v_target_397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(lean_object* v_data_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_nbuckets_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_402_ = lean_array_get_size(v_data_401_);
v___x_403_ = lean_unsigned_to_nat(2u);
v_nbuckets_404_ = lean_nat_mul(v___x_402_, v___x_403_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_box(0);
v___x_407_ = lean_mk_array(v_nbuckets_404_, v___x_406_);
v___x_408_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v___x_405_, v_data_401_, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(lean_object* v_m_409_, lean_object* v_a_410_, lean_object* v_b_411_){
_start:
{
lean_object* v_size_412_; lean_object* v_buckets_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_456_; 
v_size_412_ = lean_ctor_get(v_m_409_, 0);
v_buckets_413_ = lean_ctor_get(v_m_409_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_m_409_);
if (v_isSharedCheck_456_ == 0)
{
v___x_415_ = v_m_409_;
v_isShared_416_ = v_isSharedCheck_456_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_buckets_413_);
lean_inc(v_size_412_);
lean_dec(v_m_409_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_456_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v_fold_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; size_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v_bkt_430_; uint8_t v___x_431_; 
v___x_417_ = lean_array_get_size(v_buckets_413_);
v___x_418_ = l_Lean_ExprStructEq_hash(v_a_410_);
v___x_419_ = 32ULL;
v___x_420_ = lean_uint64_shift_right(v___x_418_, v___x_419_);
v_fold_421_ = lean_uint64_xor(v___x_418_, v___x_420_);
v___x_422_ = 16ULL;
v___x_423_ = lean_uint64_shift_right(v_fold_421_, v___x_422_);
v___x_424_ = lean_uint64_xor(v_fold_421_, v___x_423_);
v___x_425_ = lean_uint64_to_usize(v___x_424_);
v___x_426_ = lean_usize_of_nat(v___x_417_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_sub(v___x_426_, v___x_427_);
v___x_429_ = lean_usize_land(v___x_425_, v___x_428_);
v_bkt_430_ = lean_array_uget_borrowed(v_buckets_413_, v___x_429_);
v___x_431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_410_, v_bkt_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v_size_x27_433_; lean_object* v___x_434_; lean_object* v_buckets_x27_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v_size_x27_433_ = lean_nat_add(v_size_412_, v___x_432_);
lean_dec(v_size_412_);
lean_inc(v_bkt_430_);
v___x_434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_434_, 0, v_a_410_);
lean_ctor_set(v___x_434_, 1, v_b_411_);
lean_ctor_set(v___x_434_, 2, v_bkt_430_);
v_buckets_x27_435_ = lean_array_uset(v_buckets_413_, v___x_429_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(4u);
v___x_437_ = lean_nat_mul(v_size_x27_433_, v___x_436_);
v___x_438_ = lean_unsigned_to_nat(3u);
v___x_439_ = lean_nat_div(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_array_get_size(v_buckets_x27_435_);
v___x_441_ = lean_nat_dec_le(v___x_439_, v___x_440_);
lean_dec(v___x_439_);
if (v___x_441_ == 0)
{
lean_object* v_val_442_; lean_object* v___x_444_; 
v_val_442_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_buckets_x27_435_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_val_442_);
lean_ctor_set(v___x_415_, 0, v_size_x27_433_);
v___x_444_ = v___x_415_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_size_x27_433_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_val_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
else
{
lean_object* v___x_447_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_buckets_x27_435_);
lean_ctor_set(v___x_415_, 0, v_size_x27_433_);
v___x_447_ = v___x_415_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_size_x27_433_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_buckets_x27_435_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v___x_449_; lean_object* v_buckets_x27_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
lean_inc(v_bkt_430_);
v___x_449_ = lean_box(0);
v_buckets_x27_450_ = lean_array_uset(v_buckets_413_, v___x_429_, v___x_449_);
v___x_451_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_410_, v_b_411_, v_bkt_430_);
v___x_452_ = lean_array_uset(v_buckets_x27_450_, v___x_429_, v___x_451_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_452_);
v___x_454_ = v___x_415_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_size_412_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg(lean_object* v_decl_457_, uint8_t v_isLet_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v_givenNames_468_; lean_object* v_decls_469_; lean_object* v_valueMap_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_488_; 
v___x_462_ = lean_st_ref_take(v_a_460_);
v_givenNames_468_ = lean_ctor_get(v___x_462_, 0);
v_decls_469_ = lean_ctor_get(v___x_462_, 1);
v_valueMap_470_ = lean_ctor_get(v___x_462_, 2);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_488_ == 0)
{
v___x_472_ = v___x_462_;
v_isShared_473_ = v_isSharedCheck_488_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_valueMap_470_);
lean_inc(v_decls_469_);
lean_inc(v_givenNames_468_);
lean_dec(v___x_462_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_488_;
goto v_resetjp_471_;
}
v___jp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_st_ref_set(v_a_460_, v_snd_465_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_fst_464_);
return v___x_467_;
}
v_resetjp_471_:
{
uint8_t v_merge_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_merge_474_ = lean_ctor_get_uint8(v_a_459_, 6);
v___x_475_ = lean_box(0);
lean_inc_ref(v_decl_457_);
v___x_476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_476_, 0, v_decl_457_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*1, v_isLet_458_);
v___x_477_ = lean_array_push(v_decls_469_, v___x_476_);
if (v_merge_474_ == 0)
{
lean_object* v___x_479_; 
lean_dec_ref(v_decl_457_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v___x_477_);
v___x_479_ = v___x_472_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_givenNames_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_valueMap_470_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
v_fst_464_ = v___x_475_;
v_snd_465_ = v___x_479_;
goto v___jp_463_;
}
}
else
{
uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_481_ = 0;
v___x_482_ = l_Lean_LocalDecl_value(v_decl_457_, v___x_481_);
v___x_483_ = l_Lean_LocalDecl_fvarId(v_decl_457_);
lean_dec_ref(v_decl_457_);
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_470_, v___x_482_, v___x_483_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 2, v___x_484_);
lean_ctor_set(v___x_472_, 1, v___x_477_);
v___x_486_ = v___x_472_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_givenNames_468_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
v_fst_464_ = v___x_475_;
v_snd_465_ = v___x_486_;
goto v___jp_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg___boxed(lean_object* v_decl_489_, lean_object* v_isLet_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
uint8_t v_isLet_boxed_494_; lean_object* v_res_495_; 
v_isLet_boxed_494_ = lean_unbox(v_isLet_490_);
v_res_495_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_489_, v_isLet_boxed_494_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl(lean_object* v_decl_496_, uint8_t v_isLet_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_496_, v_isLet_497_, v_a_498_, v_a_500_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___boxed(lean_object* v_decl_507_, lean_object* v_isLet_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
uint8_t v_isLet_boxed_517_; lean_object* v_res_518_; 
v_isLet_boxed_517_ = lean_unbox(v_isLet_508_);
v_res_518_ = l_Lean_Meta_ExtractLets_addDecl(v_decl_507_, v_isLet_boxed_517_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0(lean_object* v_00_u03b2_519_, lean_object* v_m_520_, lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_m_520_, v_a_521_, v_b_522_);
return v___x_523_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(lean_object* v_00_u03b2_524_, lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_525_, v_x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_528_, lean_object* v_a_529_, lean_object* v_x_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(v_00_u03b2_528_, v_a_529_, v_x_530_);
lean_dec(v_x_530_);
lean_dec_ref(v_a_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1(lean_object* v_00_u03b2_533_, lean_object* v_data_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_data_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2(lean_object* v_00_u03b2_536_, lean_object* v_a_537_, lean_object* v_b_538_, lean_object* v_x_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_537_, v_b_538_, v_x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_541_, lean_object* v_i_542_, lean_object* v_source_543_, lean_object* v_target_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v_i_542_, v_source_543_, v_target_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(v_x_547_, v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(lean_object* v_k_550_, lean_object* v_t_551_){
_start:
{
if (lean_obj_tag(v_t_551_) == 0)
{
lean_object* v_k_552_; lean_object* v_l_553_; lean_object* v_r_554_; uint8_t v___x_555_; 
v_k_552_ = lean_ctor_get(v_t_551_, 1);
v_l_553_ = lean_ctor_get(v_t_551_, 3);
v_r_554_ = lean_ctor_get(v_t_551_, 4);
v___x_555_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_550_, v_k_552_);
switch(v___x_555_)
{
case 0:
{
v_t_551_ = v_l_553_;
goto _start;
}
case 1:
{
uint8_t v___x_557_; 
v___x_557_ = 1;
return v___x_557_;
}
default: 
{
v_t_551_ = v_r_554_;
goto _start;
}
}
}
else
{
uint8_t v___x_559_; 
v___x_559_ = 0;
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg___boxed(lean_object* v_k_560_, lean_object* v_t_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_560_, v_t_561_);
lean_dec(v_t_561_);
lean_dec(v_k_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(lean_object* v___x_564_, lean_object* v_e_565_){
_start:
{
uint8_t v___x_566_; lean_object* v_d_568_; lean_object* v_b_569_; 
v___x_566_ = l_Lean_Expr_hasFVar(v_e_565_);
if (v___x_566_ == 0)
{
return v___x_566_;
}
else
{
switch(lean_obj_tag(v_e_565_))
{
case 7:
{
lean_object* v_binderType_572_; lean_object* v_body_573_; 
v_binderType_572_ = lean_ctor_get(v_e_565_, 1);
v_body_573_ = lean_ctor_get(v_e_565_, 2);
v_d_568_ = v_binderType_572_;
v_b_569_ = v_body_573_;
goto v___jp_567_;
}
case 6:
{
lean_object* v_binderType_574_; lean_object* v_body_575_; 
v_binderType_574_ = lean_ctor_get(v_e_565_, 1);
v_body_575_ = lean_ctor_get(v_e_565_, 2);
v_d_568_ = v_binderType_574_;
v_b_569_ = v_body_575_;
goto v___jp_567_;
}
case 10:
{
lean_object* v_expr_576_; 
v_expr_576_ = lean_ctor_get(v_e_565_, 1);
v_e_565_ = v_expr_576_;
goto _start;
}
case 8:
{
lean_object* v_type_578_; lean_object* v_value_579_; lean_object* v_body_580_; uint8_t v___x_581_; 
v_type_578_ = lean_ctor_get(v_e_565_, 1);
v_value_579_ = lean_ctor_get(v_e_565_, 2);
v_body_580_ = lean_ctor_get(v_e_565_, 3);
v___x_581_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_type_578_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
v___x_582_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_value_579_);
if (v___x_582_ == 0)
{
v_e_565_ = v_body_580_;
goto _start;
}
else
{
return v___x_566_;
}
}
else
{
return v___x_566_;
}
}
case 5:
{
lean_object* v_fn_584_; lean_object* v_arg_585_; uint8_t v___x_586_; 
v_fn_584_ = lean_ctor_get(v_e_565_, 0);
v_arg_585_ = lean_ctor_get(v_e_565_, 1);
v___x_586_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_fn_584_);
if (v___x_586_ == 0)
{
v_e_565_ = v_arg_585_;
goto _start;
}
else
{
return v___x_566_;
}
}
case 11:
{
lean_object* v_struct_588_; 
v_struct_588_ = lean_ctor_get(v_e_565_, 2);
v_e_565_ = v_struct_588_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_590_; uint8_t v___x_591_; 
v_fvarId_590_ = lean_ctor_get(v_e_565_, 0);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_fvarId_590_, v___x_564_);
return v___x_591_;
}
default: 
{
uint8_t v___x_592_; 
v___x_592_ = 0;
return v___x_592_;
}
}
}
v___jp_567_:
{
uint8_t v___x_570_; 
v___x_570_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_d_568_);
if (v___x_570_ == 0)
{
v_e_565_ = v_b_569_;
goto _start;
}
else
{
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1___boxed(lean_object* v___x_593_, lean_object* v_e_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_593_, v_e_594_);
lean_dec_ref(v_e_594_);
lean_dec(v___x_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(lean_object* v_as_597_, size_t v_sz_598_, size_t v_i_599_, lean_object* v_b_600_){
_start:
{
lean_object* v_a_603_; uint8_t v___x_607_; 
v___x_607_ = lean_usize_dec_lt(v_i_599_, v_sz_598_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v_b_600_);
return v___x_608_;
}
else
{
lean_object* v_snd_609_; lean_object* v_fst_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_644_; 
v_snd_609_ = lean_ctor_get(v_b_600_, 1);
v_fst_610_ = lean_ctor_get(v_b_600_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_b_600_);
if (v_isSharedCheck_644_ == 0)
{
v___x_612_ = v_b_600_;
v_isShared_613_ = v_isSharedCheck_644_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snd_609_);
lean_inc(v_fst_610_);
lean_dec(v_b_600_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_644_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_643_; 
v_fst_614_ = lean_ctor_get(v_snd_609_, 0);
v_snd_615_ = lean_ctor_get(v_snd_609_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_snd_609_);
if (v_isSharedCheck_643_ == 0)
{
v___x_617_ = v_snd_609_;
v_isShared_618_ = v_isSharedCheck_643_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snd_615_);
lean_inc(v_fst_614_);
lean_dec(v_snd_609_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_643_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_a_619_; lean_object* v_decl_620_; uint8_t v___y_622_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_a_619_ = lean_array_uget_borrowed(v_as_597_, v_i_599_);
v_decl_620_ = lean_ctor_get(v_a_619_, 0);
v___x_639_ = l_Lean_LocalDecl_type(v_decl_620_);
v___x_640_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_610_, v___x_639_);
lean_dec_ref(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = l_Lean_LocalDecl_value(v_decl_620_, v___x_640_);
v___x_642_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_610_, v___x_641_);
lean_dec_ref(v___x_641_);
v___y_622_ = v___x_642_;
goto v___jp_621_;
}
else
{
v___y_622_ = v___x_640_;
goto v___jp_621_;
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_625_; 
lean_inc(v_a_619_);
v___x_623_ = lean_array_push(v_fst_614_, v_a_619_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_623_);
v___x_625_ = v___x_617_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_snd_615_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_625_);
v___x_627_ = v___x_612_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_fst_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v_a_603_ = v___x_627_;
goto v___jp_602_;
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
lean_inc(v_a_619_);
v___x_630_ = lean_array_push(v_snd_615_, v_a_619_);
v___x_631_ = l_Lean_LocalDecl_fvarId(v_decl_620_);
v___x_632_ = l_Lean_FVarIdSet_insert(v_fst_610_, v___x_631_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_630_);
v___x_634_ = v___x_617_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_fst_614_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_630_);
v___x_634_ = v_reuseFailAlloc_638_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_634_);
lean_ctor_set(v___x_612_, 0, v___x_632_);
v___x_636_ = v___x_612_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v_a_603_ = v___x_636_;
goto v___jp_602_;
}
}
}
}
}
}
}
v___jp_602_:
{
size_t v___x_604_; size_t v___x_605_; 
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_add(v_i_599_, v___x_604_);
v_i_599_ = v___x_605_;
v_b_600_ = v_a_603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(lean_object* v_as_645_, lean_object* v_sz_646_, lean_object* v_i_647_, lean_object* v_b_648_, lean_object* v___y_649_){
_start:
{
size_t v_sz_boxed_650_; size_t v_i_boxed_651_; lean_object* v_res_652_; 
v_sz_boxed_650_ = lean_unbox_usize(v_sz_646_);
lean_dec(v_sz_646_);
v_i_boxed_651_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_645_, v_sz_boxed_650_, v_i_boxed_651_, v_b_648_);
lean_dec_ref(v_as_645_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object* v_fvar_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; lean_object* v_decls_667_; lean_object* v_fvarSet_668_; lean_object* v_fvarSet_669_; lean_object* v___x_670_; lean_object* v___x_671_; size_t v_sz_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_666_ = lean_st_ref_get(v_a_660_);
v_decls_667_ = lean_ctor_get(v___x_666_, 1);
lean_inc_ref(v_decls_667_);
lean_dec(v___x_666_);
v_fvarSet_668_ = lean_box(1);
v_fvarSet_669_ = l_Lean_FVarIdSet_insert(v_fvarSet_668_, v_fvar_657_);
v___x_670_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__1));
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_fvarSet_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v_sz_672_ = lean_array_size(v_decls_667_);
v___x_673_ = ((size_t)0ULL);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_decls_667_, v_sz_672_, v___x_673_, v___x_671_);
lean_dec_ref(v_decls_667_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_697_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_697_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_697_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_697_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v_snd_680_; lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v_givenNames_683_; lean_object* v_valueMap_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_695_; 
v___x_679_ = lean_st_ref_take(v_a_660_);
v_snd_680_ = lean_ctor_get(v_a_675_, 1);
lean_inc(v_snd_680_);
lean_dec(v_a_675_);
v_fst_681_ = lean_ctor_get(v_snd_680_, 0);
lean_inc(v_fst_681_);
v_snd_682_ = lean_ctor_get(v_snd_680_, 1);
lean_inc(v_snd_682_);
lean_dec(v_snd_680_);
v_givenNames_683_ = lean_ctor_get(v___x_679_, 0);
v_valueMap_684_ = lean_ctor_get(v___x_679_, 2);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_679_, 1);
lean_dec(v_unused_696_);
v___x_686_ = v___x_679_;
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_valueMap_684_);
lean_inc(v_givenNames_683_);
lean_dec(v___x_679_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_fst_681_);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_givenNames_683_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_valueMap_684_);
v___x_689_ = v_reuseFailAlloc_694_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_st_ref_set(v_a_660_, v___x_689_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_snd_682_);
v___x_692_ = v___x_677_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_snd_682_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_a_698_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_674_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_674_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object* v_fvar_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_ExtractLets_flushDecls(v_fvar_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_715_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object* v_00_u03b2_716_, lean_object* v_k_717_, lean_object* v_t_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_717_, v_t_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object* v_00_u03b2_720_, lean_object* v_k_721_, lean_object* v_t_722_){
_start:
{
uint8_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(v_00_u03b2_720_, v_k_721_, v_t_722_);
lean_dec(v_t_722_);
lean_dec(v_k_721_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object* v_as_725_, size_t v_sz_726_, size_t v_i_727_, lean_object* v_b_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_725_, v_sz_726_, v_i_727_, v_b_728_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object* v_as_738_, lean_object* v_sz_739_, lean_object* v_i_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
size_t v_sz_boxed_750_; size_t v_i_boxed_751_; lean_object* v_res_752_; 
v_sz_boxed_750_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_751_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_738_, v_sz_boxed_750_, v_i_boxed_751_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v_as_738_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object* v_x_753_){
_start:
{
lean_object* v_decl_754_; 
v_decl_754_ = lean_ctor_get(v_x_753_, 0);
lean_inc_ref(v_decl_754_);
return v_decl_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object* v_x_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(v_x_755_);
lean_dec_ref(v_x_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object* v_lctx_757_, lean_object* v_x1_758_, lean_object* v_x2_759_){
_start:
{
lean_object* v_decl_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_decl_760_ = lean_ctor_get(v_x2_759_, 0);
v___x_761_ = l_Lean_LocalDecl_fvarId(v_decl_760_);
v___x_762_ = l_Lean_LocalContext_contains(v_lctx_757_, v___x_761_);
lean_dec(v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_array_push(v_x1_758_, v_x2_759_);
return v___x_763_;
}
else
{
lean_dec_ref(v_x2_759_);
return v_x1_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object* v_lctx_764_, lean_object* v_x1_765_, lean_object* v_x2_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(v_lctx_764_, v_x1_765_, v_x2_766_);
lean_dec_ref(v_lctx_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_k_790_, lean_object* v_decls_791_, lean_object* v_lctx_792_){
_start:
{
lean_object* v___y_794_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_array_get_size(v_decls_791_);
v___x_803_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_804_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_805_ = lean_nat_dec_lt(v___x_801_, v___x_802_);
if (v___x_805_ == 0)
{
lean_dec_ref(v_lctx_792_);
lean_dec_ref(v_decls_791_);
v___y_794_ = v___x_803_;
goto v___jp_793_;
}
else
{
lean_object* v___f_806_; uint8_t v___x_807_; 
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_806_, 0, v_lctx_792_);
v___x_807_ = lean_nat_dec_le(v___x_802_, v___x_802_);
if (v___x_807_ == 0)
{
if (v___x_805_ == 0)
{
lean_dec_ref(v___f_806_);
lean_dec_ref(v_decls_791_);
v___y_794_ = v___x_803_;
goto v___jp_793_;
}
else
{
size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
v___x_808_ = ((size_t)0ULL);
v___x_809_ = lean_usize_of_nat(v___x_802_);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_804_, v___f_806_, v_decls_791_, v___x_808_, v___x_809_, v___x_803_);
v___y_794_ = v___x_810_;
goto v___jp_793_;
}
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((size_t)0ULL);
v___x_812_ = lean_usize_of_nat(v___x_802_);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_804_, v___f_806_, v_decls_791_, v___x_811_, v___x_812_, v___x_803_);
v___y_794_ = v___x_813_;
goto v___jp_793_;
}
}
v___jp_793_:
{
lean_object* v___x_795_; size_t v_sz_796_; size_t v___x_797_; lean_object* v_decls_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_795_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_796_ = lean_array_size(v___y_794_);
v___x_797_ = ((size_t)0ULL);
v_decls_798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_795_, v___f_787_, v_sz_796_, v___x_797_, v___y_794_);
v___x_799_ = lean_array_to_list(v_decls_798_);
v___x_800_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_788_, v_inst_789_, v___x_799_, v_k_790_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_decls_818_, lean_object* v_k_819_){
_start:
{
lean_object* v_toBind_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___x_823_; 
v_toBind_820_ = lean_ctor_get(v_inst_815_, 1);
lean_inc(v_toBind_820_);
v___f_821_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_822_, 0, v___f_821_);
lean_closure_set(v___f_822_, 1, v_inst_816_);
lean_closure_set(v___f_822_, 2, v_inst_815_);
lean_closure_set(v___f_822_, 3, v_k_819_);
lean_closure_set(v___f_822_, 4, v_decls_818_);
v___x_823_ = lean_apply_4(v_toBind_820_, lean_box(0), lean_box(0), v_inst_817_, v___f_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_824_, lean_object* v_00_u03b1_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_decls_829_, lean_object* v_k_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_826_, v_inst_827_, v_inst_828_, v_decls_829_, v_k_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_832_, size_t v_i_833_, size_t v_stop_834_, lean_object* v_b_835_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = lean_usize_dec_eq(v_i_833_, v_stop_834_);
if (v___x_836_ == 0)
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v_decl_840_; uint8_t v_isLet_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_sub(v_i_833_, v___x_837_);
v___x_839_ = lean_array_uget_borrowed(v_as_832_, v___x_838_);
v_decl_840_ = lean_ctor_get(v___x_839_, 0);
v_isLet_841_ = lean_ctor_get_uint8(v___x_839_, sizeof(void*)*1);
v___x_842_ = l_Lean_LocalDecl_userName(v_decl_840_);
v___x_843_ = l_Lean_LocalDecl_type(v_decl_840_);
v___x_844_ = l_Lean_LocalDecl_value(v_decl_840_, v___x_836_);
lean_inc_ref(v_decl_840_);
v___x_845_ = l_Lean_LocalDecl_toExpr(v_decl_840_);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_mk_empty_array_with_capacity(v___x_846_);
v___x_848_ = lean_array_push(v___x_847_, v___x_845_);
v___x_849_ = lean_expr_abstract(v_b_835_, v___x_848_);
lean_dec_ref(v___x_848_);
lean_dec_ref(v_b_835_);
if (v_isLet_841_ == 0)
{
uint8_t v___x_850_; lean_object* v___x_851_; 
v___x_850_ = 1;
v___x_851_ = l_Lean_Expr_letE___override(v___x_842_, v___x_843_, v___x_844_, v___x_849_, v___x_850_);
v_i_833_ = v___x_838_;
v_b_835_ = v___x_851_;
goto _start;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Expr_letE___override(v___x_842_, v___x_843_, v___x_844_, v___x_849_, v___x_836_);
v_i_833_ = v___x_838_;
v_b_835_ = v___x_853_;
goto _start;
}
}
else
{
return v_b_835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object* v_as_855_, lean_object* v_i_856_, lean_object* v_stop_857_, lean_object* v_b_858_){
_start:
{
size_t v_i_boxed_859_; size_t v_stop_boxed_860_; lean_object* v_res_861_; 
v_i_boxed_859_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_stop_boxed_860_ = lean_unbox_usize(v_stop_857_);
lean_dec(v_stop_857_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_855_, v_i_boxed_859_, v_stop_boxed_860_, v_b_858_);
lean_dec_ref(v_as_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object* v_decls_862_, lean_object* v_e_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_array_get_size(v_decls_862_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_nat_dec_lt(v___x_865_, v___x_864_);
if (v___x_866_ == 0)
{
return v_e_863_;
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_usize_of_nat(v___x_864_);
v___x_868_ = ((size_t)0ULL);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_862_, v___x_867_, v___x_868_, v_e_863_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object* v_decls_870_, lean_object* v_e_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_870_, v_e_871_);
lean_dec_ref(v_decls_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object* v_fvarId_873_, size_t v_sz_874_, size_t v_i_875_, lean_object* v_bs_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_lt(v_i_875_, v_sz_874_);
if (v___x_877_ == 0)
{
return v_bs_876_;
}
else
{
lean_object* v_v_878_; lean_object* v_decl_879_; lean_object* v___x_880_; lean_object* v_bs_x27_881_; lean_object* v___y_883_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_v_878_ = lean_array_uget(v_bs_876_, v_i_875_);
v_decl_879_ = lean_ctor_get(v_v_878_, 0);
v___x_880_ = lean_unsigned_to_nat(0u);
v_bs_x27_881_ = lean_array_uset(v_bs_876_, v_i_875_, v___x_880_);
v___x_888_ = l_Lean_LocalDecl_fvarId(v_decl_879_);
v___x_889_ = l_Lean_instBEqFVarId_beq(v___x_888_, v_fvarId_873_);
lean_dec(v___x_888_);
if (v___x_889_ == 0)
{
v___y_883_ = v_v_878_;
goto v___jp_882_;
}
else
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_inc_ref(v_decl_879_);
v_isSharedCheck_896_ = !lean_is_exclusive(v_v_878_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_v_878_, 0);
lean_dec(v_unused_897_);
v___x_891_ = v_v_878_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_dec(v_v_878_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_decl_879_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*1, v___x_889_);
v___y_883_ = v___x_894_;
goto v___jp_882_;
}
}
}
v___jp_882_:
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_875_, v___x_884_);
v___x_886_ = lean_array_uset(v_bs_x27_881_, v_i_875_, v___y_883_);
v_i_875_ = v___x_885_;
v_bs_876_ = v___x_886_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object* v_fvarId_898_, lean_object* v_sz_899_, lean_object* v_i_900_, lean_object* v_bs_901_){
_start:
{
size_t v_sz_boxed_902_; size_t v_i_boxed_903_; lean_object* v_res_904_; 
v_sz_boxed_902_ = lean_unbox_usize(v_sz_899_);
lean_dec(v_sz_899_);
v_i_boxed_903_ = lean_unbox_usize(v_i_900_);
lean_dec(v_i_900_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_898_, v_sz_boxed_902_, v_i_boxed_903_, v_bs_901_);
lean_dec(v_fvarId_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object* v_fvarId_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_givenNames_909_; lean_object* v_decls_910_; lean_object* v_valueMap_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_924_; 
v___x_908_ = lean_st_ref_take(v_a_906_);
v_givenNames_909_ = lean_ctor_get(v___x_908_, 0);
v_decls_910_ = lean_ctor_get(v___x_908_, 1);
v_valueMap_911_ = lean_ctor_get(v___x_908_, 2);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_924_ == 0)
{
v___x_913_ = v___x_908_;
v_isShared_914_ = v_isSharedCheck_924_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_valueMap_911_);
lean_inc(v_decls_910_);
lean_inc(v_givenNames_909_);
lean_dec(v___x_908_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_924_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
size_t v_sz_915_; size_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v_sz_915_ = lean_array_size(v_decls_910_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_905_, v_sz_915_, v___x_916_, v_decls_910_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v___x_917_);
v___x_919_ = v___x_913_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_givenNames_909_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_valueMap_911_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = lean_st_ref_set(v_a_906_, v___x_919_);
v___x_921_ = lean_box(0);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object* v_fvarId_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec(v_fvarId_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object* v_fvarId_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_929_, v_a_932_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object* v_fvarId_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_fvarId_939_);
return v_res_948_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0(lean_object* v_fvarId_949_, lean_object* v_x_950_){
_start:
{
lean_object* v_decl_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_decl_951_ = lean_ctor_get(v_x_950_, 0);
v___x_952_ = l_Lean_LocalDecl_fvarId(v_decl_951_);
v___x_953_ = l_Lean_instBEqFVarId_beq(v___x_952_, v_fvarId_949_);
lean_dec(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0___boxed(lean_object* v_fvarId_954_, lean_object* v_x_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0(v_fvarId_954_, v_x_955_);
lean_dec_ref(v_x_955_);
lean_dec(v_fvarId_954_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(lean_object* v___x_958_, lean_object* v_as_959_, size_t v_i_960_, size_t v_stop_961_, lean_object* v_b_962_){
_start:
{
lean_object* v___y_964_; uint8_t v___x_968_; 
v___x_968_ = lean_usize_dec_eq(v_i_960_, v_stop_961_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v_decl_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_969_ = lean_array_uget_borrowed(v_as_959_, v_i_960_);
v_decl_970_ = lean_ctor_get(v___x_969_, 0);
v___x_971_ = l_Lean_LocalDecl_fvarId(v_decl_970_);
v___x_972_ = l_Lean_LocalContext_contains(v___x_958_, v___x_971_);
lean_dec(v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
lean_inc(v___x_969_);
v___x_973_ = lean_array_push(v_b_962_, v___x_969_);
v___y_964_ = v___x_973_;
goto v___jp_963_;
}
else
{
v___y_964_ = v_b_962_;
goto v___jp_963_;
}
}
else
{
return v_b_962_;
}
v___jp_963_:
{
size_t v___x_965_; size_t v___x_966_; 
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_960_, v___x_965_);
v_i_960_ = v___x_966_;
v_b_962_ = v___y_964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2___boxed(lean_object* v___x_974_, lean_object* v_as_975_, lean_object* v_i_976_, lean_object* v_stop_977_, lean_object* v_b_978_){
_start:
{
size_t v_i_boxed_979_; size_t v_stop_boxed_980_; lean_object* v_res_981_; 
v_i_boxed_979_ = lean_unbox_usize(v_i_976_);
lean_dec(v_i_976_);
v_stop_boxed_980_ = lean_unbox_usize(v_stop_977_);
lean_dec(v_stop_977_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v___x_974_, v_as_975_, v_i_boxed_979_, v_stop_boxed_980_, v_b_978_);
lean_dec_ref(v_as_975_);
lean_dec_ref(v___x_974_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
lean_inc(v___y_985_);
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
v___x_991_ = lean_apply_8(v_x_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, lean_box(0));
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(lean_object* v_decls_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___f_1012_; lean_object* v___x_1013_; 
lean_inc(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1012_, 0, v_x_1003_);
lean_closure_set(v___f_1012_, 1, v___y_1004_);
lean_closure_set(v___f_1012_, 2, v___y_1005_);
lean_closure_set(v___f_1012_, 3, v___y_1006_);
v___x_1013_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1002_, v___f_1012_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1013_) == 0)
{
return v___x_1013_;
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___boxed(lean_object* v_decls_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v_decls_1022_, v_x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(size_t v_sz_1033_, size_t v_i_1034_, lean_object* v_bs_1035_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_usize_dec_lt(v_i_1034_, v_sz_1033_);
if (v___x_1036_ == 0)
{
return v_bs_1035_;
}
else
{
lean_object* v_v_1037_; lean_object* v_decl_1038_; lean_object* v___x_1039_; lean_object* v_bs_x27_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v_v_1037_ = lean_array_uget_borrowed(v_bs_1035_, v_i_1034_);
v_decl_1038_ = lean_ctor_get(v_v_1037_, 0);
lean_inc_ref(v_decl_1038_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v_bs_x27_1040_ = lean_array_uset(v_bs_1035_, v_i_1034_, v___x_1039_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_1034_, v___x_1041_);
v___x_1043_ = lean_array_uset(v_bs_x27_1040_, v_i_1034_, v_decl_1038_);
v_i_1034_ = v___x_1042_;
v_bs_1035_ = v___x_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0___boxed(lean_object* v_sz_1045_, lean_object* v_i_1046_, lean_object* v_bs_1047_){
_start:
{
size_t v_sz_boxed_1048_; size_t v_i_boxed_1049_; lean_object* v_res_1050_; 
v_sz_boxed_1048_ = lean_unbox_usize(v_sz_1045_);
lean_dec(v_sz_1045_);
v_i_boxed_1049_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_boxed_1048_, v_i_boxed_1049_, v_bs_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(lean_object* v_decls_1051_, lean_object* v_k_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___y_1062_; lean_object* v_lctx_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_lctx_1068_ = lean_ctor_get(v___y_1056_, 2);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_array_get_size(v_decls_1051_);
v___x_1071_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_1072_ = lean_nat_dec_lt(v___x_1069_, v___x_1070_);
if (v___x_1072_ == 0)
{
v___y_1062_ = v___x_1071_;
goto v___jp_1061_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_nat_dec_le(v___x_1070_, v___x_1070_);
if (v___x_1073_ == 0)
{
if (v___x_1072_ == 0)
{
v___y_1062_ = v___x_1071_;
goto v___jp_1061_;
}
else
{
size_t v___x_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = ((size_t)0ULL);
v___x_1075_ = lean_usize_of_nat(v___x_1070_);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v_lctx_1068_, v_decls_1051_, v___x_1074_, v___x_1075_, v___x_1071_);
v___y_1062_ = v___x_1076_;
goto v___jp_1061_;
}
}
else
{
size_t v___x_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = ((size_t)0ULL);
v___x_1078_ = lean_usize_of_nat(v___x_1070_);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v_lctx_1068_, v_decls_1051_, v___x_1077_, v___x_1078_, v___x_1071_);
v___y_1062_ = v___x_1079_;
goto v___jp_1061_;
}
}
v___jp_1061_:
{
size_t v_sz_1063_; size_t v___x_1064_; lean_object* v_decls_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_sz_1063_ = lean_array_size(v___y_1062_);
v___x_1064_ = ((size_t)0ULL);
v_decls_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_1063_, v___x_1064_, v___y_1062_);
v___x_1066_ = lean_array_to_list(v_decls_1065_);
v___x_1067_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v___x_1066_, v_k_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg___boxed(lean_object* v_decls_1080_, lean_object* v_k_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1080_, v_k_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v_decls_1080_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1091_, lean_object* v_k_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v_lctx_1102_; uint8_t v___x_1103_; 
v___x_1101_ = lean_st_ref_get(v_a_1095_);
v_lctx_1102_ = lean_ctor_get(v_a_1096_, 2);
v___x_1103_ = l_Lean_LocalContext_contains(v_lctx_1102_, v_fvarId_1091_);
if (v___x_1103_ == 0)
{
lean_object* v_decls_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_decls_1104_ = lean_ctor_get(v___x_1101_, 1);
lean_inc_ref(v_decls_1104_);
lean_dec(v___x_1101_);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1105_, 0, v_fvarId_1091_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = l_Array_findIdx_x3f_loop___redArg(v___f_1105_, v_decls_1104_, v___x_1106_);
if (lean_obj_tag(v___x_1107_) == 1)
{
lean_object* v_val_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_val_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_add(v_val_1108_, v___x_1109_);
lean_dec(v_val_1108_);
v___x_1111_ = l_Array_toSubarray___redArg(v_decls_1104_, v___x_1106_, v___x_1110_);
v___x_1112_ = l_Subarray_copy___redArg(v___x_1111_);
v___x_1113_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v___x_1112_, v_k_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec_ref(v___x_1112_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
lean_dec(v___x_1107_);
lean_dec_ref(v_decls_1104_);
lean_inc(v_a_1099_);
lean_inc_ref(v_a_1098_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
lean_inc(v_a_1095_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
v___x_1114_ = lean_apply_8(v_k_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, lean_box(0));
return v___x_1114_;
}
}
else
{
lean_object* v___x_1115_; 
lean_dec(v___x_1101_);
lean_dec(v_fvarId_1091_);
lean_inc(v_a_1099_);
lean_inc_ref(v_a_1098_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
lean_inc(v_a_1095_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
v___x_1115_ = lean_apply_8(v_k_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, lean_box(0));
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1116_, lean_object* v_k_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1116_, v_k_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1127_, lean_object* v_fvarId_1128_, lean_object* v_k_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1128_, v_k_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_fvarId_1140_, lean_object* v_k_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1139_, v_fvarId_1140_, v_k_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1(lean_object* v_00_u03b1_1151_, lean_object* v_decls_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v_decls_1152_, v_x_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_decls_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1(v_00_u03b1_1163_, v_decls_1164_, v_x_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_00_u03b1_1175_, lean_object* v_decls_1176_, lean_object* v_k_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1176_, v_k_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_00_u03b1_1187_, lean_object* v_decls_1188_, lean_object* v_k_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_00_u03b1_1187_, v_decls_1188_, v_k_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v_decls_1188_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v___x_1202_; 
v___x_1202_ = l_Lean_Expr_hasMVar(v_e_1199_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_e_1199_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; lean_object* v_mctx_1205_; lean_object* v___x_1206_; lean_object* v_fst_1207_; lean_object* v_snd_1208_; lean_object* v___x_1209_; lean_object* v_cache_1210_; lean_object* v_zetaDeltaFVarIds_1211_; lean_object* v_postponed_1212_; lean_object* v_diag_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1222_; 
v___x_1204_ = lean_st_ref_get(v___y_1200_);
v_mctx_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_ref(v_mctx_1205_);
lean_dec(v___x_1204_);
v___x_1206_ = l_Lean_instantiateMVarsCore(v_mctx_1205_, v_e_1199_);
v_fst_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_fst_1207_);
v_snd_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_snd_1208_);
lean_dec_ref(v___x_1206_);
v___x_1209_ = lean_st_ref_take(v___y_1200_);
v_cache_1210_ = lean_ctor_get(v___x_1209_, 1);
v_zetaDeltaFVarIds_1211_ = lean_ctor_get(v___x_1209_, 2);
v_postponed_1212_ = lean_ctor_get(v___x_1209_, 3);
v_diag_1213_ = lean_ctor_get(v___x_1209_, 4);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1223_);
v___x_1215_ = v___x_1209_;
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_diag_1213_);
lean_inc(v_postponed_1212_);
lean_inc(v_zetaDeltaFVarIds_1211_);
lean_inc(v_cache_1210_);
lean_dec(v___x_1209_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v_snd_1208_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_snd_1208_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_cache_1210_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_zetaDeltaFVarIds_1211_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_postponed_1212_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_diag_1213_);
v___x_1218_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_st_ref_set(v___y_1200_, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_fst_1207_);
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1224_, v___y_1225_);
lean_dec(v___y_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1228_, v___y_1233_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1248_, size_t v_i_1249_, size_t v_stop_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_a_1261_; uint8_t v___x_1267_; 
v___x_1267_ = lean_usize_dec_eq(v_i_1249_, v_stop_1250_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_array_uget_borrowed(v_as_1248_, v_i_1249_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_box(0);
v_a_1261_ = v___x_1269_;
goto v___jp_1260_;
}
else
{
lean_object* v_val_1270_; uint8_t v___y_1272_; uint8_t v___x_1299_; 
v_val_1270_ = lean_ctor_get(v___x_1268_, 0);
v___x_1299_ = l_Lean_LocalDecl_isLet(v_val_1270_, v___x_1267_);
if (v___x_1299_ == 0)
{
v___y_1272_ = v___x_1299_;
goto v___jp_1271_;
}
else
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1270_);
if (v___x_1300_ == 0)
{
v___y_1272_ = v___x_1299_;
goto v___jp_1271_;
}
else
{
goto v___jp_1265_;
}
}
v___jp_1271_:
{
if (v___y_1272_ == 0)
{
goto v___jp_1265_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = l_Lean_LocalDecl_value(v_val_1270_, v___x_1267_);
v___x_1274_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1273_, v___y_1256_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v_givenNames_1277_; lean_object* v_decls_1278_; lean_object* v_valueMap_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1290_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = lean_st_ref_take(v___y_1254_);
v_givenNames_1277_ = lean_ctor_get(v___x_1276_, 0);
v_decls_1278_ = lean_ctor_get(v___x_1276_, 1);
v_valueMap_1279_ = lean_ctor_get(v___x_1276_, 2);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1281_ = v___x_1276_;
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_valueMap_1279_);
lean_inc(v_decls_1278_);
lean_inc(v_givenNames_1277_);
lean_dec(v___x_1276_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1283_ = l_Lean_LocalDecl_fvarId(v_val_1270_);
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1279_, v_a_1275_, v___x_1283_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 2, v___x_1284_);
v___x_1286_ = v___x_1281_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_givenNames_1277_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_decls_1278_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_st_ref_set(v___y_1254_, v___x_1286_);
v___x_1288_ = lean_box(0);
v_a_1261_ = v___x_1288_;
goto v___jp_1260_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1274_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1274_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v_b_1251_);
return v___x_1301_;
}
v___jp_1260_:
{
size_t v___x_1262_; size_t v___x_1263_; 
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_i_1249_, v___x_1262_);
v_i_1249_ = v___x_1263_;
v_b_1251_ = v_a_1261_;
goto _start;
}
v___jp_1265_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_box(0);
v_a_1261_ = v___x_1266_;
goto v___jp_1260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1302_, lean_object* v_i_1303_, lean_object* v_stop_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
size_t v_i_boxed_1314_; size_t v_stop_boxed_1315_; lean_object* v_res_1316_; 
v_i_boxed_1314_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_stop_boxed_1315_ = lean_unbox_usize(v_stop_1304_);
lean_dec(v_stop_1304_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1302_, v_i_boxed_1314_, v_stop_boxed_1315_, v_b_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec_ref(v_as_1302_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1317_, size_t v_i_1318_, size_t v_stop_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_a_1330_; uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_eq(v_i_1318_, v_stop_1319_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_array_uget_borrowed(v_as_1317_, v_i_1318_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_box(0);
v_a_1330_ = v___x_1338_;
goto v___jp_1329_;
}
else
{
lean_object* v_val_1339_; uint8_t v___y_1341_; uint8_t v___x_1368_; 
v_val_1339_ = lean_ctor_get(v___x_1337_, 0);
v___x_1368_ = l_Lean_LocalDecl_isLet(v_val_1339_, v___x_1336_);
if (v___x_1368_ == 0)
{
v___y_1341_ = v___x_1368_;
goto v___jp_1340_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1339_);
if (v___x_1369_ == 0)
{
v___y_1341_ = v___x_1368_;
goto v___jp_1340_;
}
else
{
goto v___jp_1334_;
}
}
v___jp_1340_:
{
if (v___y_1341_ == 0)
{
goto v___jp_1334_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = l_Lean_LocalDecl_value(v_val_1339_, v___x_1336_);
v___x_1343_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1342_, v___y_1325_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v_givenNames_1346_; lean_object* v_decls_1347_; lean_object* v_valueMap_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1359_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = lean_st_ref_take(v___y_1323_);
v_givenNames_1346_ = lean_ctor_get(v___x_1345_, 0);
v_decls_1347_ = lean_ctor_get(v___x_1345_, 1);
v_valueMap_1348_ = lean_ctor_get(v___x_1345_, 2);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1350_ = v___x_1345_;
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_valueMap_1348_);
lean_inc(v_decls_1347_);
lean_inc(v_givenNames_1346_);
lean_dec(v___x_1345_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = l_Lean_LocalDecl_fvarId(v_val_1339_);
v___x_1353_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1348_, v_a_1344_, v___x_1352_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 2, v___x_1353_);
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_givenNames_1346_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_decls_1347_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_st_ref_set(v___y_1323_, v___x_1355_);
v___x_1357_ = lean_box(0);
v_a_1330_ = v___x_1357_;
goto v___jp_1329_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1343_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1343_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_b_1320_);
return v___x_1370_;
}
v___jp_1329_:
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1318_, v___x_1331_);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1317_, v___x_1332_, v_stop_1319_, v_a_1330_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1333_;
}
v___jp_1334_:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_box(0);
v_a_1330_ = v___x_1335_;
goto v___jp_1329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1371_, lean_object* v_i_1372_, lean_object* v_stop_1373_, lean_object* v_b_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
size_t v_i_boxed_1383_; size_t v_stop_boxed_1384_; lean_object* v_res_1385_; 
v_i_boxed_1383_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_stop_boxed_1384_ = lean_unbox_usize(v_stop_1373_);
lean_dec(v_stop_1373_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1371_, v_i_boxed_1383_, v_stop_boxed_1384_, v_b_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec_ref(v_as_1371_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
lean_object* v_cs_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1416_; 
v_cs_1395_ = lean_ctor_get(v_x_1386_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_x_1386_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1397_ = v_x_1386_;
v_isShared_1398_ = v_isSharedCheck_1416_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_cs_1395_);
lean_dec(v_x_1386_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1416_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_array_get_size(v_cs_1395_);
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_nat_dec_lt(v___x_1399_, v___x_1400_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1404_; 
lean_dec_ref(v_cs_1395_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1401_);
v___x_1404_ = v___x_1397_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1401_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_le(v___x_1400_, v___x_1400_);
if (v___x_1406_ == 0)
{
if (v___x_1402_ == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v_cs_1395_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1401_);
v___x_1408_ = v___x_1397_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1401_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
lean_del_object(v___x_1397_);
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1400_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1395_, v___x_1410_, v___x_1411_, v___x_1401_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec_ref(v_cs_1395_);
return v___x_1412_;
}
}
else
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
lean_del_object(v___x_1397_);
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1400_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1395_, v___x_1413_, v___x_1414_, v___x_1401_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec_ref(v_cs_1395_);
return v___x_1415_;
}
}
}
}
else
{
lean_object* v_vs_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1438_; 
v_vs_1417_ = lean_ctor_get(v_x_1386_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1386_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1419_ = v_x_1386_;
v_isShared_1420_ = v_isSharedCheck_1438_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_vs_1417_);
lean_dec(v_x_1386_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1438_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = lean_array_get_size(v_vs_1417_);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_nat_dec_lt(v___x_1421_, v___x_1422_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v_vs_1417_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1423_);
v___x_1426_ = v___x_1419_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1423_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_le(v___x_1422_, v___x_1422_);
if (v___x_1428_ == 0)
{
if (v___x_1424_ == 0)
{
lean_object* v___x_1430_; 
lean_dec_ref(v_vs_1417_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1423_);
v___x_1430_ = v___x_1419_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1423_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
else
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
lean_del_object(v___x_1419_);
v___x_1432_ = ((size_t)0ULL);
v___x_1433_ = lean_usize_of_nat(v___x_1422_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1417_, v___x_1432_, v___x_1433_, v___x_1423_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec_ref(v_vs_1417_);
return v___x_1434_;
}
}
else
{
size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
lean_del_object(v___x_1419_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = lean_usize_of_nat(v___x_1422_);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1417_, v___x_1435_, v___x_1436_, v___x_1423_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec_ref(v_vs_1417_);
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1439_, size_t v_i_1440_, size_t v_stop_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_usize_dec_eq(v_i_1440_, v_stop_1441_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_array_uget_borrowed(v_as_1439_, v_i_1440_);
lean_inc(v___x_1452_);
v___x_1453_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1452_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; size_t v___x_1455_; size_t v___x_1456_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_add(v_i_1440_, v___x_1455_);
v_i_1440_ = v___x_1456_;
v_b_1442_ = v_a_1454_;
goto _start;
}
else
{
return v___x_1453_;
}
}
else
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_b_1442_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1459_, lean_object* v_i_1460_, lean_object* v_stop_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
size_t v_i_boxed_1471_; size_t v_stop_boxed_1472_; lean_object* v_res_1473_; 
v_i_boxed_1471_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_stop_boxed_1472_ = lean_unbox_usize(v_stop_1461_);
lean_dec(v_stop_1461_);
v_res_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1459_, v_i_boxed_1471_, v_stop_boxed_1472_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v_as_1459_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_root_1493_; lean_object* v_tail_1494_; lean_object* v___x_1495_; 
v_root_1493_ = lean_ctor_get(v_t_1484_, 0);
lean_inc_ref(v_root_1493_);
v_tail_1494_ = lean_ctor_get(v_t_1484_, 1);
lean_inc_ref(v_tail_1494_);
lean_dec_ref(v_t_1484_);
v___x_1495_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1493_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1516_; 
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v___x_1495_, 0);
lean_dec(v_unused_1517_);
v___x_1497_ = v___x_1495_;
v_isShared_1498_ = v_isSharedCheck_1516_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1495_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1516_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_array_get_size(v_tail_1494_);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_nat_dec_lt(v___x_1499_, v___x_1500_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1504_; 
lean_dec_ref(v_tail_1494_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1501_);
v___x_1504_ = v___x_1497_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_nat_dec_le(v___x_1500_, v___x_1500_);
if (v___x_1506_ == 0)
{
if (v___x_1502_ == 0)
{
lean_object* v___x_1508_; 
lean_dec_ref(v_tail_1494_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1501_);
v___x_1508_ = v___x_1497_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1501_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
else
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
lean_del_object(v___x_1497_);
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = lean_usize_of_nat(v___x_1500_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1494_, v___x_1510_, v___x_1511_, v___x_1501_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec_ref(v_tail_1494_);
return v___x_1512_;
}
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1497_);
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_of_nat(v___x_1500_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1494_, v___x_1513_, v___x_1514_, v___x_1501_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec_ref(v_tail_1494_);
return v___x_1515_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1494_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1527_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1529_, size_t v_x_1530_, size_t v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_object* v_cs_1540_; lean_object* v___x_1541_; size_t v___x_1542_; lean_object* v_j_1543_; lean_object* v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v_cs_1540_ = lean_ctor_get(v_x_1529_, 0);
lean_inc_ref(v_cs_1540_);
lean_dec_ref(v_x_1529_);
v___x_1541_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1542_ = lean_usize_shift_right(v_x_1530_, v_x_1531_);
v_j_1543_ = lean_usize_to_nat(v___x_1542_);
v___x_1544_ = lean_array_get_borrowed(v___x_1541_, v_cs_1540_, v_j_1543_);
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_shift_left(v___x_1545_, v_x_1531_);
v___x_1547_ = lean_usize_sub(v___x_1546_, v___x_1545_);
v___x_1548_ = lean_usize_land(v_x_1530_, v___x_1547_);
v___x_1549_ = ((size_t)5ULL);
v___x_1550_ = lean_usize_sub(v_x_1531_, v___x_1549_);
lean_inc(v___x_1544_);
v___x_1551_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1544_, v___x_1548_, v___x_1550_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1573_; 
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1574_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1573_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1573_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_j_1543_, v___x_1555_);
lean_dec(v_j_1543_);
v___x_1557_ = lean_array_get_size(v_cs_1540_);
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_nat_dec_lt(v___x_1556_, v___x_1557_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1561_; 
lean_dec(v___x_1556_);
lean_dec_ref(v_cs_1540_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1558_);
v___x_1561_ = v___x_1553_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1558_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
else
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_nat_dec_le(v___x_1557_, v___x_1557_);
if (v___x_1563_ == 0)
{
if (v___x_1559_ == 0)
{
lean_object* v___x_1565_; 
lean_dec(v___x_1556_);
lean_dec_ref(v_cs_1540_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1558_);
v___x_1565_ = v___x_1553_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1558_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
else
{
size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
lean_del_object(v___x_1553_);
v___x_1567_ = lean_usize_of_nat(v___x_1556_);
lean_dec(v___x_1556_);
v___x_1568_ = lean_usize_of_nat(v___x_1557_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1540_, v___x_1567_, v___x_1568_, v___x_1558_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v_cs_1540_);
return v___x_1569_;
}
}
else
{
size_t v___x_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
lean_del_object(v___x_1553_);
v___x_1570_ = lean_usize_of_nat(v___x_1556_);
lean_dec(v___x_1556_);
v___x_1571_ = lean_usize_of_nat(v___x_1557_);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1540_, v___x_1570_, v___x_1571_, v___x_1558_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v_cs_1540_);
return v___x_1572_;
}
}
}
}
else
{
lean_dec(v_j_1543_);
lean_dec_ref(v_cs_1540_);
return v___x_1551_;
}
}
else
{
lean_object* v_vs_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1596_; 
v_vs_1575_ = lean_ctor_get(v_x_1529_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1577_ = v_x_1529_;
v_isShared_1578_ = v_isSharedCheck_1596_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_vs_1575_);
lean_dec(v_x_1529_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1596_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1579_ = lean_usize_to_nat(v_x_1530_);
v___x_1580_ = lean_array_get_size(v_vs_1575_);
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_nat_dec_lt(v___x_1579_, v___x_1580_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1584_; 
lean_dec(v___x_1579_);
lean_dec_ref(v_vs_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1584_ = v___x_1577_;
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
uint8_t v___x_1586_; 
v___x_1586_ = lean_nat_dec_le(v___x_1580_, v___x_1580_);
if (v___x_1586_ == 0)
{
if (v___x_1582_ == 0)
{
lean_object* v___x_1588_; 
lean_dec(v___x_1579_);
lean_dec_ref(v_vs_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1588_ = v___x_1577_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1581_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
else
{
size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
lean_del_object(v___x_1577_);
v___x_1590_ = lean_usize_of_nat(v___x_1579_);
lean_dec(v___x_1579_);
v___x_1591_ = lean_usize_of_nat(v___x_1580_);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1575_, v___x_1590_, v___x_1591_, v___x_1581_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v_vs_1575_);
return v___x_1592_;
}
}
else
{
size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
lean_del_object(v___x_1577_);
v___x_1593_ = lean_usize_of_nat(v___x_1579_);
lean_dec(v___x_1579_);
v___x_1594_ = lean_usize_of_nat(v___x_1580_);
v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1575_, v___x_1593_, v___x_1594_, v___x_1581_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v_vs_1575_);
return v___x_1595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1597_, lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_x_10794__boxed_1608_; size_t v_x_10795__boxed_1609_; lean_object* v_res_1610_; 
v_x_10794__boxed_1608_ = lean_unbox_usize(v_x_1598_);
lean_dec(v_x_1598_);
v_x_10795__boxed_1609_ = lean_unbox_usize(v_x_1599_);
lean_dec(v_x_1599_);
v_res_1610_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1597_, v_x_10794__boxed_1608_, v_x_10795__boxed_1609_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1611_, lean_object* v_start_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = lean_nat_dec_eq(v_start_1612_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v_root_1623_; lean_object* v_tail_1624_; size_t v_shift_1625_; lean_object* v_tailOff_1626_; uint8_t v___x_1627_; 
v_root_1623_ = lean_ctor_get(v_t_1611_, 0);
lean_inc_ref(v_root_1623_);
v_tail_1624_ = lean_ctor_get(v_t_1611_, 1);
lean_inc_ref(v_tail_1624_);
v_shift_1625_ = lean_ctor_get_usize(v_t_1611_, 4);
v_tailOff_1626_ = lean_ctor_get(v_t_1611_, 3);
lean_inc(v_tailOff_1626_);
lean_dec_ref(v_t_1611_);
v___x_1627_ = lean_nat_dec_le(v_tailOff_1626_, v_start_1612_);
if (v___x_1627_ == 0)
{
size_t v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_tailOff_1626_);
v___x_1628_ = lean_usize_of_nat(v_start_1612_);
v___x_1629_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1623_, v___x_1628_, v_shift_1625_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1649_; 
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v___x_1629_, 0);
lean_dec(v_unused_1650_);
v___x_1631_ = v___x_1629_;
v_isShared_1632_ = v_isSharedCheck_1649_;
goto v_resetjp_1630_;
}
else
{
lean_dec(v___x_1629_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1649_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = lean_array_get_size(v_tail_1624_);
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_nat_dec_lt(v___x_1621_, v___x_1633_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v_tail_1624_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1634_);
v___x_1637_ = v___x_1631_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1634_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_le(v___x_1633_, v___x_1633_);
if (v___x_1639_ == 0)
{
if (v___x_1635_ == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v_tail_1624_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1634_);
v___x_1641_ = v___x_1631_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1634_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1631_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = lean_usize_of_nat(v___x_1633_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1624_, v___x_1643_, v___x_1644_, v___x_1634_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec_ref(v_tail_1624_);
return v___x_1645_;
}
}
else
{
size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
lean_del_object(v___x_1631_);
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = lean_usize_of_nat(v___x_1633_);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1624_, v___x_1646_, v___x_1647_, v___x_1634_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec_ref(v_tail_1624_);
return v___x_1648_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1624_);
return v___x_1629_;
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
lean_dec_ref(v_root_1623_);
v___x_1651_ = lean_nat_sub(v_start_1612_, v_tailOff_1626_);
lean_dec(v_tailOff_1626_);
v___x_1652_ = lean_array_get_size(v_tail_1624_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_nat_dec_lt(v___x_1651_, v___x_1652_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_dec(v___x_1651_);
lean_dec_ref(v_tail_1624_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
return v___x_1655_;
}
else
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_nat_dec_le(v___x_1652_, v___x_1652_);
if (v___x_1656_ == 0)
{
if (v___x_1654_ == 0)
{
lean_object* v___x_1657_; 
lean_dec(v___x_1651_);
lean_dec_ref(v_tail_1624_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1653_);
return v___x_1657_;
}
else
{
size_t v___x_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_usize_of_nat(v___x_1651_);
lean_dec(v___x_1651_);
v___x_1659_ = lean_usize_of_nat(v___x_1652_);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1624_, v___x_1658_, v___x_1659_, v___x_1653_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec_ref(v_tail_1624_);
return v___x_1660_;
}
}
else
{
size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = lean_usize_of_nat(v___x_1651_);
lean_dec(v___x_1651_);
v___x_1662_ = lean_usize_of_nat(v___x_1652_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1624_, v___x_1661_, v___x_1662_, v___x_1653_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec_ref(v_tail_1624_);
return v___x_1663_;
}
}
}
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1611_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1665_, lean_object* v_start_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1665_, v_start_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_start_1666_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1676_, lean_object* v_start_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_decls_1686_; lean_object* v___x_1687_; 
v_decls_1686_ = lean_ctor_get(v_lctx_1676_, 1);
lean_inc_ref(v_decls_1686_);
lean_dec_ref(v_lctx_1676_);
v___x_1687_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1686_, v_start_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1687_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1718_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1720_){
_start:
{
lean_object* v___f_1721_; lean_object* v___x_1722_; 
v___f_1721_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1722_ = lean_find_expr(v___f_1721_, v_e_1720_);
if (lean_obj_tag(v___x_1722_) == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
else
{
uint8_t v___x_1724_; 
lean_dec_ref(v___x_1722_);
v___x_1724_ = 1;
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1725_){
_start:
{
uint8_t v_res_1726_; lean_object* v_r_1727_; 
v_res_1726_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1725_);
lean_dec_ref(v_e_1725_);
v_r_1727_ = lean_box(v_res_1726_);
return v_r_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1731_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
v___x_1738_ = lean_apply_9(v_k_1728_, v_b_1732_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, lean_box(0));
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v_b_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v_b_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1750_, uint8_t v_bi_1751_, lean_object* v_type_1752_, lean_object* v_k_1753_, uint8_t v_kind_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___f_1763_; lean_object* v___x_1764_; 
lean_inc(v___y_1757_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1763_, 0, v_k_1753_);
lean_closure_set(v___f_1763_, 1, v___y_1755_);
lean_closure_set(v___f_1763_, 2, v___y_1756_);
lean_closure_set(v___f_1763_, 3, v___y_1757_);
v___x_1764_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1750_, v_bi_1751_, v_type_1752_, v___f_1763_, v_kind_1754_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1764_) == 0)
{
return v___x_1764_;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1773_, lean_object* v_bi_1774_, lean_object* v_type_1775_, lean_object* v_k_1776_, lean_object* v_kind_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
uint8_t v_bi_boxed_1786_; uint8_t v_kind_boxed_1787_; lean_object* v_res_1788_; 
v_bi_boxed_1786_ = lean_unbox(v_bi_1774_);
v_kind_boxed_1787_ = lean_unbox(v_kind_1777_);
v_res_1788_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1773_, v_bi_boxed_1786_, v_type_1775_, v_k_1776_, v_kind_boxed_1787_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1789_, lean_object* v_name_1790_, uint8_t v_bi_1791_, lean_object* v_type_1792_, lean_object* v_k_1793_, uint8_t v_kind_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1790_, v_bi_1791_, v_type_1792_, v_k_1793_, v_kind_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1804_, lean_object* v_name_1805_, lean_object* v_bi_1806_, lean_object* v_type_1807_, lean_object* v_k_1808_, lean_object* v_kind_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
uint8_t v_bi_boxed_1818_; uint8_t v_kind_boxed_1819_; lean_object* v_res_1820_; 
v_bi_boxed_1818_ = lean_unbox(v_bi_1806_);
v_kind_boxed_1819_ = lean_unbox(v_kind_1809_);
v_res_1820_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1804_, v_name_1805_, v_bi_boxed_1818_, v_type_1807_, v_k_1808_, v_kind_boxed_1819_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1821_, lean_object* v_e_1822_, lean_object* v___f_1823_, lean_object* v_____r_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
if (v_types_1821_ == 0)
{
lean_object* v___x_1833_; 
lean_inc_ref(v_e_1822_);
v___x_1833_ = l_Lean_Meta_isType(v_e_1822_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1844_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_unbox(v_a_1834_);
lean_dec(v_a_1834_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_del_object(v___x_1836_);
lean_dec_ref(v_e_1822_);
v___x_1839_ = lean_box(0);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
v___x_1840_ = lean_apply_9(v___f_1823_, v___x_1839_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, lean_box(0));
return v___x_1840_;
}
else
{
lean_object* v___x_1842_; 
lean_dec_ref(v___f_1823_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v_e_1822_);
v___x_1842_ = v___x_1836_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_e_1822_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v___f_1823_);
lean_dec_ref(v_e_1822_);
v_a_1845_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1833_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1833_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec_ref(v_e_1822_);
v___x_1853_ = lean_box(0);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
v___x_1854_ = lean_apply_9(v___f_1823_, v___x_1853_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, lean_box(0));
return v___x_1854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1855_, lean_object* v_e_1856_, lean_object* v___f_1857_, lean_object* v_____r_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v_types_boxed_1867_; lean_object* v_res_1868_; 
v_types_boxed_1867_ = lean_unbox(v_types_1855_);
v_res_1868_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1867_, v_e_1856_, v___f_1857_, v_____r_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1868_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1869_, uint8_t v___y_1870_){
_start:
{
if (v___y_1869_ == 0)
{
if (v___y_1870_ == 0)
{
uint8_t v___x_1871_; 
v___x_1871_ = 1;
return v___x_1871_;
}
else
{
return v___y_1869_;
}
}
else
{
return v___y_1870_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
uint8_t v___y_50691__boxed_1874_; uint8_t v___y_50692__boxed_1875_; uint8_t v_res_1876_; lean_object* v_r_1877_; 
v___y_50691__boxed_1874_ = lean_unbox(v___y_1872_);
v___y_50692__boxed_1875_ = lean_unbox(v___y_1873_);
v_res_1876_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_50691__boxed_1874_, v___y_50692__boxed_1875_);
v_r_1877_ = lean_box(v_res_1876_);
return v_r_1877_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_instMonadEIO(lean_box(0));
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_toApplicative_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1969_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1897_ = l_StateRefT_x27_instMonad___redArg(v___x_1896_);
v_toApplicative_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1897_, 1);
lean_dec(v_unused_1970_);
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1969_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_toApplicative_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1969_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_toFunctor_1902_; lean_object* v_toSeq_1903_; lean_object* v_toSeqLeft_1904_; lean_object* v_toSeqRight_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1967_; 
v_toFunctor_1902_ = lean_ctor_get(v_toApplicative_1898_, 0);
v_toSeq_1903_ = lean_ctor_get(v_toApplicative_1898_, 2);
v_toSeqLeft_1904_ = lean_ctor_get(v_toApplicative_1898_, 3);
v_toSeqRight_1905_ = lean_ctor_get(v_toApplicative_1898_, 4);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_toApplicative_1898_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_toApplicative_1898_, 1);
lean_dec(v_unused_1968_);
v___x_1907_ = v_toApplicative_1898_;
v_isShared_1908_ = v_isSharedCheck_1967_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_toSeqRight_1905_);
lean_inc(v_toSeqLeft_1904_);
lean_inc(v_toSeq_1903_);
lean_inc(v_toFunctor_1902_);
lean_dec(v_toApplicative_1898_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1967_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___f_1909_; lean_object* v___f_1910_; lean_object* v___f_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v___f_1914_; lean_object* v___f_1915_; lean_object* v___f_1916_; lean_object* v___x_1918_; 
v___f_1909_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1910_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1902_);
v___f_1911_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1911_, 0, v_toFunctor_1902_);
v___f_1912_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1912_, 0, v_toFunctor_1902_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___f_1911_);
lean_ctor_set(v___x_1913_, 1, v___f_1912_);
v___f_1914_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1914_, 0, v_toSeqRight_1905_);
v___f_1915_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1915_, 0, v_toSeqLeft_1904_);
v___f_1916_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1916_, 0, v_toSeq_1903_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 4, v___f_1914_);
lean_ctor_set(v___x_1907_, 3, v___f_1915_);
lean_ctor_set(v___x_1907_, 2, v___f_1916_);
lean_ctor_set(v___x_1907_, 1, v___f_1909_);
lean_ctor_set(v___x_1907_, 0, v___x_1913_);
v___x_1918_ = v___x_1907_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___f_1909_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v___f_1916_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v___f_1915_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v___f_1914_);
v___x_1918_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___f_1910_);
lean_ctor_set(v___x_1900_, 0, v___x_1918_);
v___x_1920_ = v___x_1900_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___f_1910_);
v___x_1920_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v_toApplicative_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1963_; 
v___x_1921_ = l_StateRefT_x27_instMonad___redArg(v___x_1920_);
v_toApplicative_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v___x_1921_, 1);
lean_dec(v_unused_1964_);
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1963_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_toApplicative_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1963_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_toFunctor_1926_; lean_object* v_toSeq_1927_; lean_object* v_toSeqLeft_1928_; lean_object* v_toSeqRight_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1961_; 
v_toFunctor_1926_ = lean_ctor_get(v_toApplicative_1922_, 0);
v_toSeq_1927_ = lean_ctor_get(v_toApplicative_1922_, 2);
v_toSeqLeft_1928_ = lean_ctor_get(v_toApplicative_1922_, 3);
v_toSeqRight_1929_ = lean_ctor_get(v_toApplicative_1922_, 4);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_toApplicative_1922_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v_toApplicative_1922_, 1);
lean_dec(v_unused_1962_);
v___x_1931_ = v_toApplicative_1922_;
v_isShared_1932_ = v_isSharedCheck_1961_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_toSeqRight_1929_);
lean_inc(v_toSeqLeft_1928_);
lean_inc(v_toSeq_1927_);
lean_inc(v_toFunctor_1926_);
lean_dec(v_toApplicative_1922_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1961_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___f_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___f_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___f_1941_; lean_object* v___f_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___f_1947_; lean_object* v___x_1949_; 
v___f_1933_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1934_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1934_, 0, v___f_1933_);
v___x_1935_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1936_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1936_, 0, v___f_1934_);
lean_closure_set(v___f_1936_, 1, v___x_1935_);
v___f_1937_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1938_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1939_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1939_, 0, v___f_1937_);
lean_closure_set(v___f_1939_, 1, v___x_1938_);
v___f_1940_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1941_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1926_);
v___f_1942_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1942_, 0, v_toFunctor_1926_);
v___f_1943_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1943_, 0, v_toFunctor_1926_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___f_1942_);
lean_ctor_set(v___x_1944_, 1, v___f_1943_);
v___f_1945_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1945_, 0, v_toSeqRight_1929_);
v___f_1946_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1946_, 0, v_toSeqLeft_1928_);
v___f_1947_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1947_, 0, v_toSeq_1927_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 4, v___f_1945_);
lean_ctor_set(v___x_1931_, 3, v___f_1946_);
lean_ctor_set(v___x_1931_, 2, v___f_1947_);
lean_ctor_set(v___x_1931_, 1, v___f_1940_);
lean_ctor_set(v___x_1931_, 0, v___x_1944_);
v___x_1949_ = v___x_1931_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___f_1940_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v___f_1947_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v___f_1946_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v___f_1945_);
v___x_1949_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1951_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___f_1941_);
lean_ctor_set(v___x_1924_, 0, v___x_1949_);
v___x_1951_ = v___x_1924_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___f_1941_);
v___x_1951_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___f_1956_; lean_object* v___x_47579__overap_1957_; lean_object* v___x_1958_; 
v___x_1952_ = l_StateRefT_x27_instMonad___redArg(v___x_1951_);
v___x_1953_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1895_, v___f_1936_, v___f_1939_, v___x_1952_);
v___x_1954_ = l_Lean_instInhabitedExpr;
v___x_1955_ = l_instInhabitedOfMonad___redArg(v___x_1953_, v___x_1954_);
v___f_1956_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1956_, 0, v___x_1955_);
v___x_47579__overap_1957_ = lean_panic_fn_borrowed(v___f_1956_, v_msg_1886_);
lean_dec_ref(v___f_1956_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
v___x_1958_ = lean_apply_8(v___x_47579__overap_1957_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, lean_box(0));
return v___x_1958_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderName_1981_, uint8_t v_binderInfo_1982_, lean_object* v_e_1983_, lean_object* v_binderType_1984_, lean_object* v_body_1985_, lean_object* v_t_1986_, lean_object* v_b_1987_){
_start:
{
uint8_t v___y_1989_; size_t v___x_1993_; size_t v___x_1994_; uint8_t v___x_1995_; 
v___x_1993_ = lean_ptr_addr(v_binderType_1984_);
v___x_1994_ = lean_ptr_addr(v_t_1986_);
v___x_1995_ = lean_usize_dec_eq(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
v___y_1989_ = v___x_1995_;
goto v___jp_1988_;
}
else
{
size_t v___x_1996_; size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_ptr_addr(v_body_1985_);
v___x_1997_ = lean_ptr_addr(v_b_1987_);
v___x_1998_ = lean_usize_dec_eq(v___x_1996_, v___x_1997_);
v___y_1989_ = v___x_1998_;
goto v___jp_1988_;
}
v___jp_1988_:
{
if (v___y_1989_ == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Expr_lam___override(v_binderName_1981_, v_t_1986_, v_b_1987_, v_binderInfo_1982_);
return v___x_1990_;
}
else
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1982_, v_binderInfo_1982_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Expr_lam___override(v_binderName_1981_, v_t_1986_, v_b_1987_, v_binderInfo_1982_);
return v___x_1992_;
}
else
{
lean_dec_ref(v_b_1987_);
lean_dec_ref(v_t_1986_);
lean_dec(v_binderName_1981_);
lean_inc_ref(v_e_1983_);
return v_e_1983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderName_1999_, lean_object* v_binderInfo_2000_, lean_object* v_e_2001_, lean_object* v_binderType_2002_, lean_object* v_body_2003_, lean_object* v_t_2004_, lean_object* v_b_2005_){
_start:
{
uint8_t v_binderInfo_50878__boxed_2006_; lean_object* v_res_2007_; 
v_binderInfo_50878__boxed_2006_ = lean_unbox(v_binderInfo_2000_);
v_res_2007_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderName_1999_, v_binderInfo_50878__boxed_2006_, v_e_2001_, v_binderType_2002_, v_body_2003_, v_t_2004_, v_b_2005_);
lean_dec_ref(v_body_2003_);
lean_dec_ref(v_binderType_2002_);
lean_dec_ref(v_e_2001_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderName_2008_, uint8_t v_binderInfo_2009_, lean_object* v_e_2010_, lean_object* v_binderType_2011_, lean_object* v_body_2012_, lean_object* v_t_2013_, lean_object* v_b_2014_){
_start:
{
uint8_t v___y_2016_; size_t v___x_2020_; size_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = lean_ptr_addr(v_binderType_2011_);
v___x_2021_ = lean_ptr_addr(v_t_2013_);
v___x_2022_ = lean_usize_dec_eq(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
v___y_2016_ = v___x_2022_;
goto v___jp_2015_;
}
else
{
size_t v___x_2023_; size_t v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = lean_ptr_addr(v_body_2012_);
v___x_2024_ = lean_ptr_addr(v_b_2014_);
v___x_2025_ = lean_usize_dec_eq(v___x_2023_, v___x_2024_);
v___y_2016_ = v___x_2025_;
goto v___jp_2015_;
}
v___jp_2015_:
{
if (v___y_2016_ == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Expr_forallE___override(v_binderName_2008_, v_t_2013_, v_b_2014_, v_binderInfo_2009_);
return v___x_2017_;
}
else
{
uint8_t v___x_2018_; 
v___x_2018_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2009_, v_binderInfo_2009_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Expr_forallE___override(v_binderName_2008_, v_t_2013_, v_b_2014_, v_binderInfo_2009_);
return v___x_2019_;
}
else
{
lean_dec_ref(v_b_2014_);
lean_dec_ref(v_t_2013_);
lean_dec(v_binderName_2008_);
lean_inc_ref(v_e_2010_);
return v_e_2010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderName_2026_, lean_object* v_binderInfo_2027_, lean_object* v_e_2028_, lean_object* v_binderType_2029_, lean_object* v_body_2030_, lean_object* v_t_2031_, lean_object* v_b_2032_){
_start:
{
uint8_t v_binderInfo_50912__boxed_2033_; lean_object* v_res_2034_; 
v_binderInfo_50912__boxed_2033_ = lean_unbox(v_binderInfo_2027_);
v_res_2034_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderName_2026_, v_binderInfo_50912__boxed_2033_, v_e_2028_, v_binderType_2029_, v_body_2030_, v_t_2031_, v_b_2032_);
lean_dec_ref(v_body_2030_);
lean_dec_ref(v_binderType_2029_);
lean_dec_ref(v_e_2028_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_2035_, lean_object* v_type_2036_, lean_object* v_val_2037_, lean_object* v_k_2038_, uint8_t v_nondep_2039_, uint8_t v_kind_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___f_2049_; lean_object* v___x_2050_; 
lean_inc(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
v___f_2049_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2049_, 0, v_k_2038_);
lean_closure_set(v___f_2049_, 1, v___y_2041_);
lean_closure_set(v___f_2049_, 2, v___y_2042_);
lean_closure_set(v___f_2049_, 3, v___y_2043_);
v___x_2050_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2035_, v_type_2036_, v_val_2037_, v___f_2049_, v_nondep_2039_, v_kind_2040_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2050_) == 0)
{
return v___x_2050_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2059_, lean_object* v_type_2060_, lean_object* v_val_2061_, lean_object* v_k_2062_, lean_object* v_nondep_2063_, lean_object* v_kind_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
uint8_t v_nondep_boxed_2073_; uint8_t v_kind_boxed_2074_; lean_object* v_res_2075_; 
v_nondep_boxed_2073_ = lean_unbox(v_nondep_2063_);
v_kind_boxed_2074_ = lean_unbox(v_kind_2064_);
v_res_2075_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2059_, v_type_2060_, v_val_2061_, v_k_2062_, v_nondep_boxed_2073_, v_kind_boxed_2074_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = l_Lean_instInhabitedExpr;
v___x_2078_ = lean_panic_fn_borrowed(v___x_2077_, v_msg_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2079_, lean_object* v_x_2080_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_box(0);
return v___x_2081_;
}
else
{
lean_object* v_key_2082_; lean_object* v_value_2083_; lean_object* v_tail_2084_; uint8_t v___x_2085_; 
v_key_2082_ = lean_ctor_get(v_x_2080_, 0);
v_value_2083_ = lean_ctor_get(v_x_2080_, 1);
v_tail_2084_ = lean_ctor_get(v_x_2080_, 2);
v___x_2085_ = l_Lean_ExprStructEq_beq(v_key_2082_, v_a_2079_);
if (v___x_2085_ == 0)
{
v_x_2080_ = v_tail_2084_;
goto _start;
}
else
{
lean_object* v___x_2087_; 
lean_inc(v_value_2083_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_value_2083_);
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2088_, lean_object* v_x_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2088_, v_x_2089_);
lean_dec(v_x_2089_);
lean_dec_ref(v_a_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_buckets_2093_; lean_object* v___x_2094_; uint64_t v___x_2095_; uint64_t v___x_2096_; uint64_t v___x_2097_; uint64_t v_fold_2098_; uint64_t v___x_2099_; uint64_t v___x_2100_; uint64_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_buckets_2093_ = lean_ctor_get(v_m_2091_, 1);
v___x_2094_ = lean_array_get_size(v_buckets_2093_);
v___x_2095_ = l_Lean_ExprStructEq_hash(v_a_2092_);
v___x_2096_ = 32ULL;
v___x_2097_ = lean_uint64_shift_right(v___x_2095_, v___x_2096_);
v_fold_2098_ = lean_uint64_xor(v___x_2095_, v___x_2097_);
v___x_2099_ = 16ULL;
v___x_2100_ = lean_uint64_shift_right(v_fold_2098_, v___x_2099_);
v___x_2101_ = lean_uint64_xor(v_fold_2098_, v___x_2100_);
v___x_2102_ = lean_uint64_to_usize(v___x_2101_);
v___x_2103_ = lean_usize_of_nat(v___x_2094_);
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_sub(v___x_2103_, v___x_2104_);
v___x_2106_ = lean_usize_land(v___x_2102_, v___x_2105_);
v___x_2107_ = lean_array_uget_borrowed(v_buckets_2093_, v___x_2106_);
v___x_2108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2092_, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2109_, v_a_2110_);
lean_dec_ref(v_a_2110_);
lean_dec_ref(v_m_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2112_, lean_object* v_x_2113_){
_start:
{
if (lean_obj_tag(v_x_2113_) == 0)
{
uint8_t v___x_2114_; 
v___x_2114_ = 0;
return v___x_2114_;
}
else
{
lean_object* v_key_2115_; lean_object* v_tail_2116_; lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v_fst_2119_; lean_object* v_snd_2120_; uint8_t v___x_2124_; 
v_key_2115_ = lean_ctor_get(v_x_2113_, 0);
v_tail_2116_ = lean_ctor_get(v_x_2113_, 2);
v_fst_2117_ = lean_ctor_get(v_key_2115_, 0);
v_snd_2118_ = lean_ctor_get(v_key_2115_, 1);
v_fst_2119_ = lean_ctor_get(v_a_2112_, 0);
v_snd_2120_ = lean_ctor_get(v_a_2112_, 1);
v___x_2124_ = lean_unbox(v_fst_2117_);
if (v___x_2124_ == 0)
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_unbox(v_fst_2119_);
if (v___x_2125_ == 0)
{
goto v___jp_2121_;
}
else
{
v_x_2113_ = v_tail_2116_;
goto _start;
}
}
else
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_unbox(v_fst_2119_);
if (v___x_2127_ == 0)
{
v_x_2113_ = v_tail_2116_;
goto _start;
}
else
{
goto v___jp_2121_;
}
}
v___jp_2121_:
{
uint8_t v___x_2122_; 
v___x_2122_ = l_Lean_ExprStructEq_beq(v_snd_2118_, v_snd_2120_);
if (v___x_2122_ == 0)
{
v_x_2113_ = v_tail_2116_;
goto _start;
}
else
{
return v___x_2122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2129_, lean_object* v_x_2130_){
_start:
{
uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_res_2131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2129_, v_x_2130_);
lean_dec(v_x_2130_);
lean_dec_ref(v_a_2129_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2133_, lean_object* v_b_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
lean_dec(v_b_2134_);
lean_dec_ref(v_a_2133_);
return v_x_2135_;
}
else
{
lean_object* v_key_2136_; lean_object* v_value_2137_; lean_object* v_tail_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2157_; 
v_key_2136_ = lean_ctor_get(v_x_2135_, 0);
v_value_2137_ = lean_ctor_get(v_x_2135_, 1);
v_tail_2138_ = lean_ctor_get(v_x_2135_, 2);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_x_2135_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2140_ = v_x_2135_;
v_isShared_2141_ = v_isSharedCheck_2157_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_tail_2138_);
lean_inc(v_value_2137_);
lean_inc(v_key_2136_);
lean_dec(v_x_2135_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2157_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_fst_2147_; lean_object* v_snd_2148_; lean_object* v_fst_2149_; lean_object* v_snd_2150_; uint8_t v___x_2154_; 
v_fst_2147_ = lean_ctor_get(v_key_2136_, 0);
v_snd_2148_ = lean_ctor_get(v_key_2136_, 1);
v_fst_2149_ = lean_ctor_get(v_a_2133_, 0);
v_snd_2150_ = lean_ctor_get(v_a_2133_, 1);
v___x_2154_ = lean_unbox(v_fst_2147_);
if (v___x_2154_ == 0)
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_unbox(v_fst_2149_);
if (v___x_2155_ == 0)
{
goto v___jp_2151_;
}
else
{
goto v___jp_2142_;
}
}
else
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_unbox(v_fst_2149_);
if (v___x_2156_ == 0)
{
goto v___jp_2142_;
}
else
{
goto v___jp_2151_;
}
}
v___jp_2142_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2133_, v_b_2134_, v_tail_2138_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 2, v___x_2143_);
v___x_2145_ = v___x_2140_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_key_2136_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_value_2137_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
v___jp_2151_:
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lean_ExprStructEq_beq(v_snd_2148_, v_snd_2150_);
if (v___x_2152_ == 0)
{
goto v___jp_2142_;
}
else
{
lean_object* v___x_2153_; 
lean_del_object(v___x_2140_);
lean_dec(v_value_2137_);
lean_dec(v_key_2136_);
v___x_2153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2153_, 0, v_a_2133_);
lean_ctor_set(v___x_2153_, 1, v_b_2134_);
lean_ctor_set(v___x_2153_, 2, v_tail_2138_);
return v___x_2153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
if (lean_obj_tag(v_x_2159_) == 0)
{
return v_x_2158_;
}
else
{
lean_object* v_key_2160_; lean_object* v_value_2161_; lean_object* v_tail_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2193_; 
v_key_2160_ = lean_ctor_get(v_x_2159_, 0);
v_value_2161_ = lean_ctor_get(v_x_2159_, 1);
v_tail_2162_ = lean_ctor_get(v_x_2159_, 2);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_x_2159_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2164_ = v_x_2159_;
v_isShared_2165_ = v_isSharedCheck_2193_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_tail_2162_);
lean_inc(v_value_2161_);
lean_inc(v_key_2160_);
lean_dec(v_x_2159_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2193_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_fst_2166_; lean_object* v_snd_2167_; lean_object* v___x_2168_; uint64_t v___y_2170_; uint8_t v___x_2190_; 
v_fst_2166_ = lean_ctor_get(v_key_2160_, 0);
v_snd_2167_ = lean_ctor_get(v_key_2160_, 1);
v___x_2168_ = lean_array_get_size(v_x_2158_);
v___x_2190_ = lean_unbox(v_fst_2166_);
if (v___x_2190_ == 0)
{
uint64_t v___x_2191_; 
v___x_2191_ = 13ULL;
v___y_2170_ = v___x_2191_;
goto v___jp_2169_;
}
else
{
uint64_t v___x_2192_; 
v___x_2192_ = 11ULL;
v___y_2170_ = v___x_2192_;
goto v___jp_2169_;
}
v___jp_2169_:
{
uint64_t v___x_2171_; uint64_t v___x_2172_; uint64_t v___x_2173_; uint64_t v___x_2174_; uint64_t v_fold_2175_; uint64_t v___x_2176_; uint64_t v___x_2177_; uint64_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2171_ = l_Lean_ExprStructEq_hash(v_snd_2167_);
v___x_2172_ = lean_uint64_mix_hash(v___y_2170_, v___x_2171_);
v___x_2173_ = 32ULL;
v___x_2174_ = lean_uint64_shift_right(v___x_2172_, v___x_2173_);
v_fold_2175_ = lean_uint64_xor(v___x_2172_, v___x_2174_);
v___x_2176_ = 16ULL;
v___x_2177_ = lean_uint64_shift_right(v_fold_2175_, v___x_2176_);
v___x_2178_ = lean_uint64_xor(v_fold_2175_, v___x_2177_);
v___x_2179_ = lean_uint64_to_usize(v___x_2178_);
v___x_2180_ = lean_usize_of_nat(v___x_2168_);
v___x_2181_ = ((size_t)1ULL);
v___x_2182_ = lean_usize_sub(v___x_2180_, v___x_2181_);
v___x_2183_ = lean_usize_land(v___x_2179_, v___x_2182_);
v___x_2184_ = lean_array_uget_borrowed(v_x_2158_, v___x_2183_);
lean_inc(v___x_2184_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 2, v___x_2184_);
v___x_2186_ = v___x_2164_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_key_2160_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_value_2161_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_array_uset(v_x_2158_, v___x_2183_, v___x_2186_);
v_x_2158_ = v___x_2187_;
v_x_2159_ = v_tail_2162_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2194_, lean_object* v_source_2195_, lean_object* v_target_2196_){
_start:
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_array_get_size(v_source_2195_);
v___x_2198_ = lean_nat_dec_lt(v_i_2194_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_dec_ref(v_source_2195_);
lean_dec(v_i_2194_);
return v_target_2196_;
}
else
{
lean_object* v_es_2199_; lean_object* v___x_2200_; lean_object* v_source_2201_; lean_object* v_target_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_es_2199_ = lean_array_fget(v_source_2195_, v_i_2194_);
v___x_2200_ = lean_box(0);
v_source_2201_ = lean_array_fset(v_source_2195_, v_i_2194_, v___x_2200_);
v_target_2202_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2196_, v_es_2199_);
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = lean_nat_add(v_i_2194_, v___x_2203_);
lean_dec(v_i_2194_);
v_i_2194_ = v___x_2204_;
v_source_2195_ = v_source_2201_;
v_target_2196_ = v_target_2202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_nbuckets_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2207_ = lean_array_get_size(v_data_2206_);
v___x_2208_ = lean_unsigned_to_nat(2u);
v_nbuckets_2209_ = lean_nat_mul(v___x_2207_, v___x_2208_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_mk_array(v_nbuckets_2209_, v___x_2211_);
v___x_2213_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2210_, v_data_2206_, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2214_, lean_object* v_a_2215_, lean_object* v_b_2216_){
_start:
{
lean_object* v_size_2217_; lean_object* v_buckets_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2269_; 
v_size_2217_ = lean_ctor_get(v_m_2214_, 0);
v_buckets_2218_ = lean_ctor_get(v_m_2214_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_m_2214_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2220_ = v_m_2214_;
v_isShared_2221_ = v_isSharedCheck_2269_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_buckets_2218_);
lean_inc(v_size_2217_);
lean_dec(v_m_2214_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2269_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_fst_2222_; lean_object* v_snd_2223_; lean_object* v___x_2224_; uint64_t v___y_2226_; uint8_t v___x_2266_; 
v_fst_2222_ = lean_ctor_get(v_a_2215_, 0);
v_snd_2223_ = lean_ctor_get(v_a_2215_, 1);
v___x_2224_ = lean_array_get_size(v_buckets_2218_);
v___x_2266_ = lean_unbox(v_fst_2222_);
if (v___x_2266_ == 0)
{
uint64_t v___x_2267_; 
v___x_2267_ = 13ULL;
v___y_2226_ = v___x_2267_;
goto v___jp_2225_;
}
else
{
uint64_t v___x_2268_; 
v___x_2268_ = 11ULL;
v___y_2226_ = v___x_2268_;
goto v___jp_2225_;
}
v___jp_2225_:
{
uint64_t v___x_2227_; uint64_t v___x_2228_; uint64_t v___x_2229_; uint64_t v___x_2230_; uint64_t v_fold_2231_; uint64_t v___x_2232_; uint64_t v___x_2233_; uint64_t v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; size_t v___x_2237_; size_t v___x_2238_; size_t v___x_2239_; lean_object* v_bkt_2240_; uint8_t v___x_2241_; 
v___x_2227_ = l_Lean_ExprStructEq_hash(v_snd_2223_);
v___x_2228_ = lean_uint64_mix_hash(v___y_2226_, v___x_2227_);
v___x_2229_ = 32ULL;
v___x_2230_ = lean_uint64_shift_right(v___x_2228_, v___x_2229_);
v_fold_2231_ = lean_uint64_xor(v___x_2228_, v___x_2230_);
v___x_2232_ = 16ULL;
v___x_2233_ = lean_uint64_shift_right(v_fold_2231_, v___x_2232_);
v___x_2234_ = lean_uint64_xor(v_fold_2231_, v___x_2233_);
v___x_2235_ = lean_uint64_to_usize(v___x_2234_);
v___x_2236_ = lean_usize_of_nat(v___x_2224_);
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_sub(v___x_2236_, v___x_2237_);
v___x_2239_ = lean_usize_land(v___x_2235_, v___x_2238_);
v_bkt_2240_ = lean_array_uget_borrowed(v_buckets_2218_, v___x_2239_);
v___x_2241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2215_, v_bkt_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v_size_x27_2243_; lean_object* v___x_2244_; lean_object* v_buckets_x27_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v___x_2242_ = lean_unsigned_to_nat(1u);
v_size_x27_2243_ = lean_nat_add(v_size_2217_, v___x_2242_);
lean_dec(v_size_2217_);
lean_inc(v_bkt_2240_);
v___x_2244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2244_, 0, v_a_2215_);
lean_ctor_set(v___x_2244_, 1, v_b_2216_);
lean_ctor_set(v___x_2244_, 2, v_bkt_2240_);
v_buckets_x27_2245_ = lean_array_uset(v_buckets_2218_, v___x_2239_, v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(4u);
v___x_2247_ = lean_nat_mul(v_size_x27_2243_, v___x_2246_);
v___x_2248_ = lean_unsigned_to_nat(3u);
v___x_2249_ = lean_nat_div(v___x_2247_, v___x_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_array_get_size(v_buckets_x27_2245_);
v___x_2251_ = lean_nat_dec_le(v___x_2249_, v___x_2250_);
lean_dec(v___x_2249_);
if (v___x_2251_ == 0)
{
lean_object* v_val_2252_; lean_object* v___x_2254_; 
v_val_2252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2245_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v_val_2252_);
lean_ctor_set(v___x_2220_, 0, v_size_x27_2243_);
v___x_2254_ = v___x_2220_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_size_x27_2243_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_val_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
else
{
lean_object* v___x_2257_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v_buckets_x27_2245_);
lean_ctor_set(v___x_2220_, 0, v_size_x27_2243_);
v___x_2257_ = v___x_2220_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_size_x27_2243_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_buckets_x27_2245_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
else
{
lean_object* v___x_2259_; lean_object* v_buckets_x27_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_inc(v_bkt_2240_);
v___x_2259_ = lean_box(0);
v_buckets_x27_2260_ = lean_array_uset(v_buckets_2218_, v___x_2239_, v___x_2259_);
v___x_2261_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2215_, v_b_2216_, v_bkt_2240_);
v___x_2262_ = lean_array_uset(v_buckets_x27_2260_, v___x_2239_, v___x_2261_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v___x_2262_);
v___x_2264_ = v___x_2220_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_size_2217_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2270_, lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_box(0);
return v___x_2272_;
}
else
{
lean_object* v_key_2273_; lean_object* v_value_2274_; lean_object* v_tail_2275_; lean_object* v_fst_2276_; lean_object* v_snd_2277_; lean_object* v_fst_2278_; lean_object* v_snd_2279_; uint8_t v___x_2284_; 
v_key_2273_ = lean_ctor_get(v_x_2271_, 0);
v_value_2274_ = lean_ctor_get(v_x_2271_, 1);
v_tail_2275_ = lean_ctor_get(v_x_2271_, 2);
v_fst_2276_ = lean_ctor_get(v_key_2273_, 0);
v_snd_2277_ = lean_ctor_get(v_key_2273_, 1);
v_fst_2278_ = lean_ctor_get(v_a_2270_, 0);
v_snd_2279_ = lean_ctor_get(v_a_2270_, 1);
v___x_2284_ = lean_unbox(v_fst_2276_);
if (v___x_2284_ == 0)
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_unbox(v_fst_2278_);
if (v___x_2285_ == 0)
{
goto v___jp_2280_;
}
else
{
v_x_2271_ = v_tail_2275_;
goto _start;
}
}
else
{
uint8_t v___x_2287_; 
v___x_2287_ = lean_unbox(v_fst_2278_);
if (v___x_2287_ == 0)
{
v_x_2271_ = v_tail_2275_;
goto _start;
}
else
{
goto v___jp_2280_;
}
}
v___jp_2280_:
{
uint8_t v___x_2281_; 
v___x_2281_ = l_Lean_ExprStructEq_beq(v_snd_2277_, v_snd_2279_);
if (v___x_2281_ == 0)
{
v_x_2271_ = v_tail_2275_;
goto _start;
}
else
{
lean_object* v___x_2283_; 
lean_inc(v_value_2274_);
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v_value_2274_);
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2289_, v_x_2290_);
lean_dec(v_x_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_buckets_2294_; lean_object* v_fst_2295_; lean_object* v_snd_2296_; lean_object* v___x_2297_; uint64_t v___y_2299_; uint8_t v___x_2315_; 
v_buckets_2294_ = lean_ctor_get(v_m_2292_, 1);
v_fst_2295_ = lean_ctor_get(v_a_2293_, 0);
v_snd_2296_ = lean_ctor_get(v_a_2293_, 1);
v___x_2297_ = lean_array_get_size(v_buckets_2294_);
v___x_2315_ = lean_unbox(v_fst_2295_);
if (v___x_2315_ == 0)
{
uint64_t v___x_2316_; 
v___x_2316_ = 13ULL;
v___y_2299_ = v___x_2316_;
goto v___jp_2298_;
}
else
{
uint64_t v___x_2317_; 
v___x_2317_ = 11ULL;
v___y_2299_ = v___x_2317_;
goto v___jp_2298_;
}
v___jp_2298_:
{
uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; uint64_t v___x_2303_; uint64_t v_fold_2304_; uint64_t v___x_2305_; uint64_t v___x_2306_; uint64_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v___x_2310_; size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2300_ = l_Lean_ExprStructEq_hash(v_snd_2296_);
v___x_2301_ = lean_uint64_mix_hash(v___y_2299_, v___x_2300_);
v___x_2302_ = 32ULL;
v___x_2303_ = lean_uint64_shift_right(v___x_2301_, v___x_2302_);
v_fold_2304_ = lean_uint64_xor(v___x_2301_, v___x_2303_);
v___x_2305_ = 16ULL;
v___x_2306_ = lean_uint64_shift_right(v_fold_2304_, v___x_2305_);
v___x_2307_ = lean_uint64_xor(v_fold_2304_, v___x_2306_);
v___x_2308_ = lean_uint64_to_usize(v___x_2307_);
v___x_2309_ = lean_usize_of_nat(v___x_2297_);
v___x_2310_ = ((size_t)1ULL);
v___x_2311_ = lean_usize_sub(v___x_2309_, v___x_2310_);
v___x_2312_ = lean_usize_land(v___x_2308_, v___x_2311_);
v___x_2313_ = lean_array_uget_borrowed(v_buckets_2294_, v___x_2312_);
v___x_2314_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2293_, v___x_2313_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2318_, v_a_2319_);
lean_dec_ref(v_a_2319_);
lean_dec_ref(v_m_2318_);
return v_res_2320_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2321_; lean_object* v_dummy_2322_; 
v___x_2321_ = lean_box(0);
v_dummy_2322_ = l_Lean_Expr_sort___override(v___x_2321_);
return v_dummy_2322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2323_, lean_object* v_fst_2324_, lean_object* v_fvars_2325_, lean_object* v_a_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_a_2337_; uint8_t v___x_2341_; 
v___x_2341_ = lean_nat_dec_lt(v_a_2326_, v_upperBound_2323_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_dec(v_a_2326_);
lean_dec(v_fvars_2325_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v_b_2327_);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v_binderInfo_2345_; uint8_t v___x_2346_; 
v___x_2343_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2344_ = lean_array_get_borrowed(v___x_2343_, v_fst_2324_, v_a_2326_);
v_binderInfo_2345_ = lean_ctor_get_uint8(v___x_2344_, sizeof(void*)*2);
v___x_2346_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2345_);
if (v___x_2346_ == 0)
{
v_a_2337_ = v_b_2327_;
goto v___jp_2336_;
}
else
{
uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = 0;
v___x_2348_ = l_Lean_instInhabitedExpr;
v___x_2349_ = lean_array_get_borrowed(v___x_2348_, v_b_2327_, v_a_2326_);
lean_inc(v___x_2349_);
lean_inc(v_fvars_2325_);
v___x_2350_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2325_, v___x_2349_, v___x_2347_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = lean_array_set(v_b_2327_, v_a_2326_, v_a_2351_);
v_a_2337_ = v___x_2352_;
goto v___jp_2336_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_b_2327_);
lean_dec(v_a_2326_);
lean_dec(v_fvars_2325_);
v_a_2353_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2350_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2350_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_unsigned_to_nat(1u);
v___x_2339_ = lean_nat_add(v_a_2326_, v___x_2338_);
lean_dec(v_a_2326_);
v_a_2326_ = v___x_2339_;
v_b_2327_ = v_a_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2361_, size_t v_sz_2362_, size_t v_i_2363_, lean_object* v_bs_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_usize_dec_lt(v_i_2363_, v_sz_2362_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_dec(v_fvars_2361_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_bs_2364_);
return v___x_2374_;
}
else
{
uint8_t v___x_2375_; lean_object* v_v_2376_; lean_object* v___x_2377_; 
v___x_2375_ = 0;
v_v_2376_ = lean_array_uget_borrowed(v_bs_2364_, v_i_2363_);
lean_inc(v_v_2376_);
lean_inc(v_fvars_2361_);
v___x_2377_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2361_, v_v_2376_, v___x_2375_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v_bs_x27_2380_; size_t v___x_2381_; size_t v___x_2382_; lean_object* v___x_2383_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = lean_unsigned_to_nat(0u);
v_bs_x27_2380_ = lean_array_uset(v_bs_2364_, v_i_2363_, v___x_2379_);
v___x_2381_ = ((size_t)1ULL);
v___x_2382_ = lean_usize_add(v_i_2363_, v___x_2381_);
v___x_2383_ = lean_array_uset(v_bs_x27_2380_, v_i_2363_, v_a_2378_);
v_i_2363_ = v___x_2382_;
v_bs_2364_ = v___x_2383_;
goto _start;
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v_bs_2364_);
lean_dec(v_fvars_2361_);
v_a_2385_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2377_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2377_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2393_, lean_object* v_f_2394_, lean_object* v_args_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
uint8_t v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = 0;
lean_inc_ref(v_f_2394_);
lean_inc(v_fvars_2393_);
v___x_2405_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2393_, v_f_2394_, v___x_2404_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2405_) == 0)
{
uint8_t v_implicits_2406_; 
v_implicits_2406_ = lean_ctor_get_uint8(v_a_2396_, 2);
if (v_implicits_2406_ == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2405_);
lean_inc(v_a_2402_);
lean_inc_ref(v_a_2401_);
lean_inc(v_a_2400_);
lean_inc_ref(v_a_2399_);
v___x_2408_ = lean_infer_type(v_f_2394_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref(v___x_2408_);
v___x_2410_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2409_, v_args_2395_, v___x_2404_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v_fst_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___x_2410_);
v_fst_2412_ = lean_ctor_get(v_a_2411_, 0);
lean_inc(v_fst_2412_);
lean_dec(v_a_2411_);
v___x_2413_ = lean_array_get_size(v_args_2395_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2413_, v_fst_2412_, v_fvars_2393_, v___x_2414_, v_args_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_fst_2412_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = l_Lean_mkAppN(v_a_2407_, v_a_2416_);
lean_dec(v_a_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_a_2407_);
v_a_2425_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2415_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2415_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_a_2407_);
lean_dec_ref(v_args_2395_);
lean_dec(v_fvars_2393_);
v_a_2433_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2410_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2410_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_dec(v_a_2407_);
lean_dec_ref(v_args_2395_);
lean_dec(v_fvars_2393_);
return v___x_2408_;
}
}
else
{
lean_object* v_a_2441_; size_t v_sz_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
lean_dec_ref(v_f_2394_);
v_a_2441_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2441_);
lean_dec_ref(v___x_2405_);
v_sz_2442_ = lean_array_size(v_args_2395_);
v___x_2443_ = ((size_t)0ULL);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2393_, v_sz_2442_, v___x_2443_, v_args_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2453_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2453_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2453_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = l_Lean_mkAppN(v_a_2441_, v_a_2445_);
lean_dec(v_a_2445_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2449_);
v___x_2451_ = v___x_2447_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_a_2441_);
v_a_2454_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2444_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2444_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2395_);
lean_dec_ref(v_f_2394_);
lean_dec(v_fvars_2393_);
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2462_, lean_object* v_f_2463_, lean_object* v_args_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2462_, v_f_2463_, v_args_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2474_, lean_object* v_b_2475_, uint8_t v___x_2476_, lean_object* v_mk_2477_, lean_object* v_a_2478_, lean_object* v_x_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_inc_ref(v_x_2479_);
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_x_2479_);
lean_ctor_set(v___x_2488_, 1, v_fvars_2474_);
v___x_2489_ = lean_expr_instantiate1(v_b_2475_, v_x_2479_);
v___x_2490_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2488_, v___x_2489_, v___x_2476_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2490_) == 0)
{
uint8_t v_lift_2491_; 
v_lift_2491_ = lean_ctor_get_uint8(v___y_2480_, 10);
if (v_lift_2491_ == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2504_; 
v_a_2492_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2494_ = v___x_2490_;
v_isShared_2495_ = v_isSharedCheck_2504_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2490_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2504_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2496_ = lean_unsigned_to_nat(1u);
v___x_2497_ = lean_mk_empty_array_with_capacity(v___x_2496_);
v___x_2498_ = lean_array_push(v___x_2497_, v_x_2479_);
v___x_2499_ = lean_expr_abstract(v_a_2492_, v___x_2498_);
lean_dec_ref(v___x_2498_);
lean_dec(v_a_2492_);
v___x_2500_ = lean_apply_2(v_mk_2477_, v_a_2478_, v___x_2499_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2500_);
v___x_2502_ = v___x_2494_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v___x_2490_);
v___x_2506_ = l_Lean_Expr_fvarId_x21(v_x_2479_);
v___x_2507_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2506_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2521_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2521_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2521_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2512_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2508_, v_a_2505_);
lean_dec(v_a_2508_);
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_mk_empty_array_with_capacity(v___x_2513_);
v___x_2515_ = lean_array_push(v___x_2514_, v_x_2479_);
v___x_2516_ = lean_expr_abstract(v___x_2512_, v___x_2515_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2512_);
v___x_2517_ = lean_apply_2(v_mk_2477_, v_a_2478_, v___x_2516_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2517_);
v___x_2519_ = v___x_2510_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_a_2505_);
lean_dec_ref(v_x_2479_);
lean_dec_ref(v_a_2478_);
lean_dec_ref(v_mk_2477_);
v_a_2522_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2507_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2507_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2479_);
lean_dec_ref(v_a_2478_);
lean_dec_ref(v_mk_2477_);
return v___x_2490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2530_, lean_object* v_b_2531_, lean_object* v___x_2532_, lean_object* v_mk_2533_, lean_object* v_a_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
uint8_t v___x_51502__boxed_2544_; lean_object* v_res_2545_; 
v___x_51502__boxed_2544_ = lean_unbox(v___x_2532_);
v_res_2545_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2530_, v_b_2531_, v___x_51502__boxed_2544_, v_mk_2533_, v_a_2534_, v_x_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v_b_2531_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2546_, lean_object* v_n_2547_, lean_object* v_t_2548_, lean_object* v_b_2549_, uint8_t v_i_2550_, lean_object* v_mk_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
uint8_t v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = 0;
lean_inc(v_fvars_2546_);
v___x_2561_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2546_, v_t_2548_, v___x_2560_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2561_) == 0)
{
uint8_t v_underBinder_2562_; 
v_underBinder_2562_ = lean_ctor_get_uint8(v_a_2552_, 4);
if (v_underBinder_2562_ == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_n_2547_);
lean_dec(v_fvars_2546_);
v_a_2563_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2565_ = v___x_2561_;
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = lean_apply_2(v_mk_2551_, v_a_2563_, v_b_2549_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2567_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___f_2574_; uint8_t v___x_2575_; lean_object* v___x_2576_; 
v_a_2572_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_n(v_a_2572_, 2);
lean_dec_ref(v___x_2561_);
v___x_2573_ = lean_box(v___x_2560_);
v___f_2574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2574_, 0, v_fvars_2546_);
lean_closure_set(v___f_2574_, 1, v_b_2549_);
lean_closure_set(v___f_2574_, 2, v___x_2573_);
lean_closure_set(v___f_2574_, 3, v_mk_2551_);
lean_closure_set(v___f_2574_, 4, v_a_2572_);
v___x_2575_ = 0;
v___x_2576_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2547_, v_i_2550_, v_a_2572_, v___f_2574_, v___x_2575_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2576_;
}
}
else
{
lean_dec_ref(v_mk_2551_);
lean_dec_ref(v_b_2549_);
lean_dec(v_n_2547_);
lean_dec(v_fvars_2546_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2577_, lean_object* v_n_2578_, lean_object* v_t_2579_, lean_object* v_b_2580_, lean_object* v_i_2581_, lean_object* v_mk_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
uint8_t v_i_boxed_2591_; lean_object* v_res_2592_; 
v_i_boxed_2591_ = lean_unbox(v_i_2581_);
v_res_2592_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2577_, v_n_2578_, v_t_2579_, v_b_2580_, v_i_boxed_2591_, v_mk_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2593_, lean_object* v_e_2594_, lean_object* v_topLevel_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
uint8_t v_topLevel_boxed_2604_; lean_object* v_res_2605_; 
v_topLevel_boxed_2604_ = lean_unbox(v_topLevel_2595_);
v_res_2605_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2593_, v_e_2594_, v_topLevel_boxed_2604_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
return v_res_2605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2610_ = lean_unsigned_to_nat(27u);
v___x_2611_ = lean_unsigned_to_nat(1946u);
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2614_ = l_mkPanicMessageWithDecl(v___x_2613_, v___x_2612_, v___x_2611_, v___x_2610_, v___x_2609_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2615_, lean_object* v_fvars_2616_, lean_object* v_b_2617_, uint8_t v___x_2618_, lean_object* v_e_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, uint8_t v_isLet_2622_, uint8_t v_topLevel_2623_, lean_object* v_x_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
if (v_fst_2615_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc_ref(v_x_2624_);
v___x_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_x_2624_);
lean_ctor_set(v___x_2633_, 1, v_fvars_2616_);
v___x_2634_ = lean_expr_instantiate1(v_b_2617_, v_x_2624_);
v___x_2635_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2633_, v___x_2634_, v___x_2618_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2635_) == 0)
{
if (lean_obj_tag(v_e_2619_) == 8)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2671_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2671_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2671_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_declName_2640_; lean_object* v_type_2641_; lean_object* v_value_2642_; lean_object* v_body_2643_; uint8_t v_nondep_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___y_2650_; size_t v___x_2665_; size_t v___x_2666_; uint8_t v___x_2667_; 
v_declName_2640_ = lean_ctor_get(v_e_2619_, 0);
v_type_2641_ = lean_ctor_get(v_e_2619_, 1);
v_value_2642_ = lean_ctor_get(v_e_2619_, 2);
v_body_2643_ = lean_ctor_get(v_e_2619_, 3);
v_nondep_2644_ = lean_ctor_get_uint8(v_e_2619_, sizeof(void*)*4 + 8);
v___x_2645_ = lean_unsigned_to_nat(1u);
v___x_2646_ = lean_mk_empty_array_with_capacity(v___x_2645_);
v___x_2647_ = lean_array_push(v___x_2646_, v_x_2624_);
v___x_2648_ = lean_expr_abstract(v_a_2636_, v___x_2647_);
lean_dec_ref(v___x_2647_);
lean_dec(v_a_2636_);
v___x_2665_ = lean_ptr_addr(v_type_2641_);
v___x_2666_ = lean_ptr_addr(v_a_2620_);
v___x_2667_ = lean_usize_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
v___y_2650_ = v___x_2667_;
goto v___jp_2649_;
}
else
{
size_t v___x_2668_; size_t v___x_2669_; uint8_t v___x_2670_; 
v___x_2668_ = lean_ptr_addr(v_value_2642_);
v___x_2669_ = lean_ptr_addr(v_a_2621_);
v___x_2670_ = lean_usize_dec_eq(v___x_2668_, v___x_2669_);
v___y_2650_ = v___x_2670_;
goto v___jp_2649_;
}
v___jp_2649_:
{
if (v___y_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
lean_inc(v_declName_2640_);
lean_dec_ref(v_e_2619_);
v___x_2651_ = l_Lean_Expr_letE___override(v_declName_2640_, v_a_2620_, v_a_2621_, v___x_2648_, v_nondep_2644_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2651_);
v___x_2653_ = v___x_2638_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
else
{
size_t v___x_2655_; size_t v___x_2656_; uint8_t v___x_2657_; 
v___x_2655_ = lean_ptr_addr(v_body_2643_);
v___x_2656_ = lean_ptr_addr(v___x_2648_);
v___x_2657_ = lean_usize_dec_eq(v___x_2655_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
lean_inc(v_declName_2640_);
lean_dec_ref(v_e_2619_);
v___x_2658_ = l_Lean_Expr_letE___override(v_declName_2640_, v_a_2620_, v_a_2621_, v___x_2648_, v_nondep_2644_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2658_);
v___x_2660_ = v___x_2638_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
else
{
lean_object* v___x_2663_; 
lean_dec_ref(v___x_2648_);
lean_dec_ref(v_a_2621_);
lean_dec_ref(v_a_2620_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v_e_2619_);
v___x_2663_ = v___x_2638_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_e_2619_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
else
{
lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v_x_2624_);
lean_dec_ref(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec_ref(v_e_2619_);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2681_);
v___x_2673_ = v___x_2635_;
v_isShared_2674_ = v_isSharedCheck_2680_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v___x_2635_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2680_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2676_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2675_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2676_);
v___x_2678_ = v___x_2673_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_dec_ref(v_x_2624_);
lean_dec_ref(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec_ref(v_e_2619_);
return v___x_2635_;
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec_ref(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec_ref(v_e_2619_);
v___x_2682_ = l_Lean_Expr_fvarId_x21(v_x_2624_);
v___x_2683_ = l_Lean_FVarId_getDecl___redArg(v___x_2682_, v___y_2628_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2685_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref(v___x_2683_);
v___x_2685_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2684_, v_isLet_2622_, v___y_2625_, v___y_2627_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec_ref(v___x_2685_);
v___x_2686_ = lean_expr_instantiate1(v_b_2617_, v_x_2624_);
lean_dec_ref(v_x_2624_);
v___x_2687_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2616_, v___x_2686_, v_topLevel_2623_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v___x_2687_;
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v_x_2624_);
lean_dec(v_fvars_2616_);
v_a_2688_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2685_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2685_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v_x_2624_);
lean_dec(v_fvars_2616_);
v_a_2696_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2683_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2683_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2704_ = _args[0];
lean_object* v_fvars_2705_ = _args[1];
lean_object* v_b_2706_ = _args[2];
lean_object* v___x_2707_ = _args[3];
lean_object* v_e_2708_ = _args[4];
lean_object* v_a_2709_ = _args[5];
lean_object* v_a_2710_ = _args[6];
lean_object* v_isLet_2711_ = _args[7];
lean_object* v_topLevel_2712_ = _args[8];
lean_object* v_x_2713_ = _args[9];
lean_object* v___y_2714_ = _args[10];
lean_object* v___y_2715_ = _args[11];
lean_object* v___y_2716_ = _args[12];
lean_object* v___y_2717_ = _args[13];
lean_object* v___y_2718_ = _args[14];
lean_object* v___y_2719_ = _args[15];
lean_object* v___y_2720_ = _args[16];
lean_object* v___y_2721_ = _args[17];
_start:
{
uint8_t v_fst_51647__boxed_2722_; uint8_t v___x_51648__boxed_2723_; uint8_t v_isLet_boxed_2724_; uint8_t v_topLevel_boxed_2725_; lean_object* v_res_2726_; 
v_fst_51647__boxed_2722_ = lean_unbox(v_fst_2704_);
v___x_51648__boxed_2723_ = lean_unbox(v___x_2707_);
v_isLet_boxed_2724_ = lean_unbox(v_isLet_2711_);
v_topLevel_boxed_2725_ = lean_unbox(v_topLevel_2712_);
v_res_2726_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_51647__boxed_2722_, v_fvars_2705_, v_b_2706_, v___x_51648__boxed_2723_, v_e_2708_, v_a_2709_, v_a_2710_, v_isLet_boxed_2724_, v_topLevel_boxed_2725_, v_x_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v_b_2706_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2727_, lean_object* v_e_2728_, uint8_t v_isLet_2729_, lean_object* v_n_2730_, lean_object* v_t_2731_, lean_object* v_v_2732_, lean_object* v_b_2733_, uint8_t v_topLevel_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; uint8_t v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = 0;
lean_inc(v_fvars_2727_);
v___x_2758_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2727_, v_t_2731_, v___x_2757_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2877_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2877_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2877_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; 
lean_inc(v_fvars_2727_);
v___x_2763_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2727_, v_v_2732_, v___x_2757_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2876_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2876_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2876_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint8_t v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; uint8_t v___y_2772_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; uint8_t v_descend_2816_; uint8_t v_underBinder_2817_; uint8_t v_usedOnly_2818_; uint8_t v_merge_2819_; uint8_t v_lift_2820_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; uint8_t v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; uint8_t v___y_2858_; 
v_descend_2816_ = lean_ctor_get_uint8(v_a_2735_, 3);
v_underBinder_2817_ = lean_ctor_get_uint8(v_a_2735_, 4);
v_usedOnly_2818_ = lean_ctor_get_uint8(v_a_2735_, 5);
v_merge_2819_ = lean_ctor_get_uint8(v_a_2735_, 6);
v_lift_2820_ = lean_ctor_get_uint8(v_a_2735_, 10);
if (v_usedOnly_2818_ == 0)
{
v___y_2858_ = v___x_2757_;
goto v___jp_2857_;
}
else
{
uint8_t v___x_2874_; 
v___x_2874_ = l_Lean_Expr_hasLooseBVars(v_b_2733_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_del_object(v___x_2766_);
lean_dec(v_a_2764_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2759_);
lean_dec(v_n_2730_);
lean_dec_ref(v_e_2728_);
v___x_2875_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2727_, v_b_2733_, v_topLevel_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
return v___x_2875_;
}
else
{
v___y_2858_ = v___x_2757_;
goto v___jp_2857_;
}
}
v___jp_2768_:
{
if (v___y_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_dec_ref(v___y_2770_);
lean_dec_ref(v_e_2728_);
v___x_2773_ = l_Lean_Expr_letE___override(v___y_2771_, v_a_2759_, v_a_2764_, v_b_2733_, v___y_2769_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2773_);
v___x_2775_ = v___x_2766_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
size_t v___x_2777_; size_t v___x_2778_; uint8_t v___x_2779_; 
v___x_2777_ = lean_ptr_addr(v___y_2770_);
lean_dec_ref(v___y_2770_);
v___x_2778_ = lean_ptr_addr(v_b_2733_);
v___x_2779_ = lean_usize_dec_eq(v___x_2777_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
lean_dec_ref(v_e_2728_);
v___x_2780_ = l_Lean_Expr_letE___override(v___y_2771_, v_a_2759_, v_a_2764_, v_b_2733_, v___y_2769_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2780_);
v___x_2782_ = v___x_2766_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
else
{
lean_object* v___x_2785_; 
lean_dec(v___y_2771_);
lean_dec(v_a_2764_);
lean_dec(v_a_2759_);
lean_dec_ref(v_b_2733_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v_e_2728_);
v___x_2785_ = v___x_2766_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_e_2728_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
v___jp_2787_:
{
if (lean_obj_tag(v_e_2728_) == 8)
{
lean_object* v_declName_2788_; lean_object* v_type_2789_; lean_object* v_value_2790_; lean_object* v_body_2791_; uint8_t v_nondep_2792_; size_t v___x_2793_; size_t v___x_2794_; uint8_t v___x_2795_; 
lean_del_object(v___x_2761_);
v_declName_2788_ = lean_ctor_get(v_e_2728_, 0);
v_type_2789_ = lean_ctor_get(v_e_2728_, 1);
v_value_2790_ = lean_ctor_get(v_e_2728_, 2);
v_body_2791_ = lean_ctor_get(v_e_2728_, 3);
v_nondep_2792_ = lean_ctor_get_uint8(v_e_2728_, sizeof(void*)*4 + 8);
v___x_2793_ = lean_ptr_addr(v_type_2789_);
v___x_2794_ = lean_ptr_addr(v_a_2759_);
v___x_2795_ = lean_usize_dec_eq(v___x_2793_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_inc(v_declName_2788_);
lean_inc_ref(v_body_2791_);
v___y_2769_ = v_nondep_2792_;
v___y_2770_ = v_body_2791_;
v___y_2771_ = v_declName_2788_;
v___y_2772_ = v___x_2795_;
goto v___jp_2768_;
}
else
{
size_t v___x_2796_; size_t v___x_2797_; uint8_t v___x_2798_; 
v___x_2796_ = lean_ptr_addr(v_value_2790_);
v___x_2797_ = lean_ptr_addr(v_a_2764_);
v___x_2798_ = lean_usize_dec_eq(v___x_2796_, v___x_2797_);
lean_inc(v_declName_2788_);
lean_inc_ref(v_body_2791_);
v___y_2769_ = v_nondep_2792_;
v___y_2770_ = v_body_2791_;
v___y_2771_ = v_declName_2788_;
v___y_2772_ = v___x_2798_;
goto v___jp_2768_;
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
lean_del_object(v___x_2766_);
lean_dec(v_a_2764_);
lean_dec(v_a_2759_);
lean_dec_ref(v_b_2733_);
lean_dec_ref(v_e_2728_);
v___x_2799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2800_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2799_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2800_);
v___x_2802_ = v___x_2761_;
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
}
v___jp_2804_:
{
uint8_t v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = 0;
v___x_2815_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2806_, v_a_2759_, v_a_2764_, v___y_2805_, v___x_2757_, v___x_2814_, v___y_2812_, v___y_2811_, v___y_2808_, v___y_2813_, v___y_2810_, v___y_2809_, v___y_2807_);
return v___x_2815_;
}
v___jp_2821_:
{
if (v_underBinder_2817_ == 0)
{
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
goto v___jp_2787_;
}
else
{
if (v_descend_2816_ == 0)
{
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
goto v___jp_2787_;
}
else
{
lean_del_object(v___x_2766_);
lean_del_object(v___x_2761_);
lean_dec_ref(v_b_2733_);
lean_dec_ref(v_e_2728_);
v___y_2805_ = v___y_2822_;
v___y_2806_ = v___y_2823_;
v___y_2807_ = v___y_2825_;
v___y_2808_ = v___y_2824_;
v___y_2809_ = v___y_2826_;
v___y_2810_ = v___y_2828_;
v___y_2811_ = v___y_2827_;
v___y_2812_ = v___y_2829_;
v___y_2813_ = v___y_2830_;
goto v___jp_2804_;
}
}
}
v___jp_2831_:
{
lean_object* v___x_2840_; 
lean_inc(v_a_2764_);
lean_inc(v_a_2759_);
v___x_2840_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2727_, v_n_2730_, v_a_2759_, v_a_2764_, v___y_2833_, v___y_2835_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v_fst_2842_; lean_object* v_snd_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___f_2847_; uint8_t v___x_2848_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref(v___x_2840_);
v_fst_2842_ = lean_ctor_get(v_a_2841_, 0);
lean_inc_n(v_fst_2842_, 2);
v_snd_2843_ = lean_ctor_get(v_a_2841_, 1);
lean_inc(v_snd_2843_);
lean_dec(v_a_2841_);
v___x_2844_ = lean_box(v___x_2757_);
v___x_2845_ = lean_box(v_isLet_2729_);
v___x_2846_ = lean_box(v_topLevel_2734_);
lean_inc(v_a_2764_);
lean_inc(v_a_2759_);
lean_inc_ref(v_e_2728_);
lean_inc_ref(v_b_2733_);
v___f_2847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2847_, 0, v_fst_2842_);
lean_closure_set(v___f_2847_, 1, v_fvars_2727_);
lean_closure_set(v___f_2847_, 2, v_b_2733_);
lean_closure_set(v___f_2847_, 3, v___x_2844_);
lean_closure_set(v___f_2847_, 4, v_e_2728_);
lean_closure_set(v___f_2847_, 5, v_a_2759_);
lean_closure_set(v___f_2847_, 6, v_a_2764_);
lean_closure_set(v___f_2847_, 7, v___x_2845_);
lean_closure_set(v___f_2847_, 8, v___x_2846_);
v___x_2848_ = lean_unbox(v_fst_2842_);
lean_dec(v_fst_2842_);
if (v___x_2848_ == 0)
{
v___y_2822_ = v___f_2847_;
v___y_2823_ = v_snd_2843_;
v___y_2824_ = v___y_2835_;
v___y_2825_ = v___y_2839_;
v___y_2826_ = v___y_2838_;
v___y_2827_ = v___y_2834_;
v___y_2828_ = v___y_2837_;
v___y_2829_ = v___y_2833_;
v___y_2830_ = v___y_2836_;
goto v___jp_2821_;
}
else
{
if (v___y_2832_ == 0)
{
lean_del_object(v___x_2766_);
lean_del_object(v___x_2761_);
lean_dec_ref(v_b_2733_);
lean_dec_ref(v_e_2728_);
v___y_2805_ = v___f_2847_;
v___y_2806_ = v_snd_2843_;
v___y_2807_ = v___y_2839_;
v___y_2808_ = v___y_2835_;
v___y_2809_ = v___y_2838_;
v___y_2810_ = v___y_2837_;
v___y_2811_ = v___y_2834_;
v___y_2812_ = v___y_2833_;
v___y_2813_ = v___y_2836_;
goto v___jp_2804_;
}
else
{
v___y_2822_ = v___f_2847_;
v___y_2823_ = v_snd_2843_;
v___y_2824_ = v___y_2835_;
v___y_2825_ = v___y_2839_;
v___y_2826_ = v___y_2838_;
v___y_2827_ = v___y_2834_;
v___y_2828_ = v___y_2837_;
v___y_2829_ = v___y_2833_;
v___y_2830_ = v___y_2836_;
goto v___jp_2821_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2766_);
lean_dec(v_a_2764_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2759_);
lean_dec_ref(v_b_2733_);
lean_dec_ref(v_e_2728_);
lean_dec(v_fvars_2727_);
v_a_2849_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2840_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2840_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
v___jp_2857_:
{
if (v_merge_2819_ == 0)
{
v___y_2832_ = v___y_2858_;
v___y_2833_ = v_a_2735_;
v___y_2834_ = v_a_2736_;
v___y_2835_ = v_a_2737_;
v___y_2836_ = v_a_2738_;
v___y_2837_ = v_a_2739_;
v___y_2838_ = v_a_2740_;
v___y_2839_ = v_a_2741_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2859_; lean_object* v_valueMap_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_st_ref_get(v_a_2737_);
v_valueMap_2860_ = lean_ctor_get(v___x_2859_, 2);
lean_inc_ref(v_valueMap_2860_);
lean_dec(v___x_2859_);
v___x_2861_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2860_, v_a_2764_);
lean_dec_ref(v_valueMap_2860_);
if (lean_obj_tag(v___x_2861_) == 1)
{
lean_del_object(v___x_2766_);
lean_dec(v_a_2764_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2759_);
lean_dec(v_n_2730_);
lean_dec_ref(v_e_2728_);
if (v_isLet_2729_ == 0)
{
lean_object* v_val_2862_; 
v_val_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_val_2862_);
lean_dec_ref(v___x_2861_);
v___y_2744_ = v_val_2862_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
v___y_2749_ = v_a_2739_;
v___y_2750_ = v_a_2740_;
v___y_2751_ = v_a_2741_;
goto v___jp_2743_;
}
else
{
if (v_lift_2820_ == 0)
{
lean_object* v_val_2863_; 
v_val_2863_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_val_2863_);
lean_dec_ref(v___x_2861_);
v___y_2744_ = v_val_2863_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
v___y_2749_ = v_a_2739_;
v___y_2750_ = v_a_2740_;
v___y_2751_ = v_a_2741_;
goto v___jp_2743_;
}
else
{
lean_object* v_val_2864_; lean_object* v___x_2865_; 
v_val_2864_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_val_2864_);
lean_dec_ref(v___x_2861_);
v___x_2865_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2864_, v_a_2737_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_dec_ref(v___x_2865_);
v___y_2744_ = v_val_2864_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
v___y_2749_ = v_a_2739_;
v___y_2750_ = v_a_2740_;
v___y_2751_ = v_a_2741_;
goto v___jp_2743_;
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_val_2864_);
lean_dec_ref(v_b_2733_);
lean_dec(v_fvars_2727_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2861_);
v___y_2832_ = v___y_2858_;
v___y_2833_ = v_a_2735_;
v___y_2834_ = v_a_2736_;
v___y_2835_ = v_a_2737_;
v___y_2836_ = v_a_2738_;
v___y_2837_ = v_a_2739_;
v___y_2838_ = v_a_2740_;
v___y_2839_ = v_a_2741_;
goto v___jp_2831_;
}
}
}
}
}
else
{
lean_del_object(v___x_2761_);
lean_dec(v_a_2759_);
lean_dec_ref(v_b_2733_);
lean_dec(v_n_2730_);
lean_dec_ref(v_e_2728_);
lean_dec(v_fvars_2727_);
return v___x_2763_;
}
}
}
else
{
lean_dec_ref(v_b_2733_);
lean_dec_ref(v_v_2732_);
lean_dec(v_n_2730_);
lean_dec_ref(v_e_2728_);
lean_dec(v_fvars_2727_);
return v___x_2758_;
}
v___jp_2743_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_inc(v___y_2744_);
v___x_2752_ = l_Lean_Expr_fvar___override(v___y_2744_);
v___x_2753_ = lean_expr_instantiate1(v_b_2733_, v___x_2752_);
lean_dec_ref(v___x_2752_);
lean_dec_ref(v_b_2733_);
v___x_2754_ = lean_box(v_topLevel_2734_);
v___x_2755_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2755_, 0, v_fvars_2727_);
lean_closure_set(v___x_2755_, 1, v___x_2753_);
lean_closure_set(v___x_2755_, 2, v___x_2754_);
v___x_2756_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2744_, v___x_2755_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2878_, lean_object* v_struct_2879_, lean_object* v___y_2880_, lean_object* v_typeName_2881_, lean_object* v_idx_2882_, lean_object* v_e_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v___y_51423__boxed_2892_; lean_object* v_res_2893_; 
v___y_51423__boxed_2892_ = lean_unbox(v___y_2880_);
v_res_2893_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2878_, v_struct_2879_, v___y_51423__boxed_2892_, v_typeName_2881_, v_idx_2882_, v_e_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
return v_res_2893_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2897_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2898_ = lean_unsigned_to_nat(75u);
v___x_2899_ = lean_unsigned_to_nat(229u);
v___x_2900_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2901_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2902_ = l_mkPanicMessageWithDecl(v___x_2901_, v___x_2900_, v___x_2899_, v___x_2898_, v___x_2897_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2903_, lean_object* v_e_2904_, lean_object* v_fvars_2905_, uint8_t v___x_2906_, uint8_t v_topLevel_2907_, uint8_t v___y_2908_, lean_object* v_____r_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_k_2919_; 
switch(lean_obj_tag(v_e_2904_))
{
case 5:
{
lean_object* v___x_2922_; lean_object* v_dummy_2923_; lean_object* v_nargs_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2922_ = l_Lean_Expr_getAppFn(v_e_2904_);
v_dummy_2923_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2924_ = l_Lean_Expr_getAppNumArgs(v_e_2904_);
lean_inc(v_nargs_2924_);
v___x_2925_ = lean_mk_array(v_nargs_2924_, v_dummy_2923_);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_sub(v_nargs_2924_, v___x_2926_);
lean_dec(v_nargs_2924_);
lean_inc_ref(v_e_2904_);
v___x_2928_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2904_, v___x_2925_, v___x_2927_);
v___x_2929_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2929_, 0, v_fvars_2905_);
lean_closure_set(v___x_2929_, 1, v___x_2922_);
lean_closure_set(v___x_2929_, 2, v___x_2928_);
v_k_2919_ = v___x_2929_;
goto v___jp_2918_;
}
case 6:
{
lean_object* v_binderName_2930_; lean_object* v_binderType_2931_; lean_object* v_body_2932_; uint8_t v_binderInfo_2933_; lean_object* v___x_2934_; lean_object* v___f_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_binderName_2930_ = lean_ctor_get(v_e_2904_, 0);
v_binderType_2931_ = lean_ctor_get(v_e_2904_, 1);
v_body_2932_ = lean_ctor_get(v_e_2904_, 2);
v_binderInfo_2933_ = lean_ctor_get_uint8(v_e_2904_, sizeof(void*)*3 + 8);
v___x_2934_ = lean_box(v_binderInfo_2933_);
lean_inc_ref_n(v_body_2932_, 2);
lean_inc_ref_n(v_binderType_2931_, 2);
lean_inc_ref(v_e_2904_);
lean_inc_n(v_binderName_2930_, 2);
v___f_2935_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2935_, 0, v_binderName_2930_);
lean_closure_set(v___f_2935_, 1, v___x_2934_);
lean_closure_set(v___f_2935_, 2, v_e_2904_);
lean_closure_set(v___f_2935_, 3, v_binderType_2931_);
lean_closure_set(v___f_2935_, 4, v_body_2932_);
v___x_2936_ = lean_box(v_binderInfo_2933_);
v___x_2937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2937_, 0, v_fvars_2905_);
lean_closure_set(v___x_2937_, 1, v_binderName_2930_);
lean_closure_set(v___x_2937_, 2, v_binderType_2931_);
lean_closure_set(v___x_2937_, 3, v_body_2932_);
lean_closure_set(v___x_2937_, 4, v___x_2936_);
lean_closure_set(v___x_2937_, 5, v___f_2935_);
v_k_2919_ = v___x_2937_;
goto v___jp_2918_;
}
case 7:
{
lean_object* v_binderName_2938_; lean_object* v_binderType_2939_; lean_object* v_body_2940_; uint8_t v_binderInfo_2941_; lean_object* v___x_2942_; lean_object* v___f_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_binderName_2938_ = lean_ctor_get(v_e_2904_, 0);
v_binderType_2939_ = lean_ctor_get(v_e_2904_, 1);
v_body_2940_ = lean_ctor_get(v_e_2904_, 2);
v_binderInfo_2941_ = lean_ctor_get_uint8(v_e_2904_, sizeof(void*)*3 + 8);
v___x_2942_ = lean_box(v_binderInfo_2941_);
lean_inc_ref_n(v_body_2940_, 2);
lean_inc_ref_n(v_binderType_2939_, 2);
lean_inc_ref(v_e_2904_);
lean_inc_n(v_binderName_2938_, 2);
v___f_2943_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2943_, 0, v_binderName_2938_);
lean_closure_set(v___f_2943_, 1, v___x_2942_);
lean_closure_set(v___f_2943_, 2, v_e_2904_);
lean_closure_set(v___f_2943_, 3, v_binderType_2939_);
lean_closure_set(v___f_2943_, 4, v_body_2940_);
v___x_2944_ = lean_box(v_binderInfo_2941_);
v___x_2945_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2945_, 0, v_fvars_2905_);
lean_closure_set(v___x_2945_, 1, v_binderName_2938_);
lean_closure_set(v___x_2945_, 2, v_binderType_2939_);
lean_closure_set(v___x_2945_, 3, v_body_2940_);
lean_closure_set(v___x_2945_, 4, v___x_2944_);
lean_closure_set(v___x_2945_, 5, v___f_2943_);
v_k_2919_ = v___x_2945_;
goto v___jp_2918_;
}
case 8:
{
uint8_t v_nondep_2946_; 
v_nondep_2946_ = lean_ctor_get_uint8(v_e_2904_, sizeof(void*)*4 + 8);
if (v_nondep_2946_ == 0)
{
lean_object* v_declName_2947_; lean_object* v_type_2948_; lean_object* v_value_2949_; lean_object* v_body_2950_; lean_object* v___x_2951_; 
v_declName_2947_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_declName_2947_);
v_type_2948_ = lean_ctor_get(v_e_2904_, 1);
lean_inc_ref(v_type_2948_);
v_value_2949_ = lean_ctor_get(v_e_2904_, 2);
lean_inc_ref(v_value_2949_);
v_body_2950_ = lean_ctor_get(v_e_2904_, 3);
lean_inc_ref(v_body_2950_);
v___x_2951_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2905_, v_e_2904_, v___x_2906_, v_declName_2947_, v_type_2948_, v_value_2949_, v_body_2950_, v_topLevel_2907_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
return v___x_2951_;
}
else
{
lean_object* v_declName_2952_; lean_object* v_type_2953_; lean_object* v_value_2954_; lean_object* v_body_2955_; lean_object* v___x_2956_; 
v_declName_2952_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_declName_2952_);
v_type_2953_ = lean_ctor_get(v_e_2904_, 1);
lean_inc_ref(v_type_2953_);
v_value_2954_ = lean_ctor_get(v_e_2904_, 2);
lean_inc_ref(v_value_2954_);
v_body_2955_ = lean_ctor_get(v_e_2904_, 3);
lean_inc_ref(v_body_2955_);
v___x_2956_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2905_, v_e_2904_, v___y_2908_, v_declName_2952_, v_type_2953_, v_value_2954_, v_body_2955_, v_topLevel_2907_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
return v___x_2956_;
}
}
case 10:
{
lean_object* v_data_2957_; lean_object* v_expr_2958_; lean_object* v___x_2959_; 
v_data_2957_ = lean_ctor_get(v_e_2904_, 0);
v_expr_2958_ = lean_ctor_get(v_e_2904_, 1);
lean_inc_ref(v_expr_2958_);
v___x_2959_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2905_, v_expr_2958_, v_topLevel_2907_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2974_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2974_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2974_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
size_t v___x_2964_; size_t v___x_2965_; uint8_t v___x_2966_; 
v___x_2964_ = lean_ptr_addr(v_expr_2958_);
v___x_2965_ = lean_ptr_addr(v_a_2960_);
v___x_2966_ = lean_usize_dec_eq(v___x_2964_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
lean_inc(v_data_2957_);
lean_dec_ref(v_e_2904_);
v___x_2967_ = l_Lean_Expr_mdata___override(v_data_2957_, v_a_2960_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2967_);
v___x_2969_ = v___x_2962_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
else
{
lean_object* v___x_2972_; 
lean_dec(v_a_2960_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v_e_2904_);
v___x_2972_ = v___x_2962_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_e_2904_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_dec_ref(v_e_2904_);
return v___x_2959_;
}
}
case 11:
{
lean_object* v_typeName_2975_; lean_object* v_idx_2976_; lean_object* v_struct_2977_; lean_object* v___x_2978_; lean_object* v___f_2979_; 
v_typeName_2975_ = lean_ctor_get(v_e_2904_, 0);
v_idx_2976_ = lean_ctor_get(v_e_2904_, 1);
v_struct_2977_ = lean_ctor_get(v_e_2904_, 2);
v___x_2978_ = lean_box(v___y_2908_);
lean_inc_ref(v_e_2904_);
lean_inc(v_idx_2976_);
lean_inc(v_typeName_2975_);
lean_inc_ref(v_struct_2977_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2979_, 0, v_fvars_2905_);
lean_closure_set(v___f_2979_, 1, v_struct_2977_);
lean_closure_set(v___f_2979_, 2, v___x_2978_);
lean_closure_set(v___f_2979_, 3, v_typeName_2975_);
lean_closure_set(v___f_2979_, 4, v_idx_2976_);
lean_closure_set(v___f_2979_, 5, v_e_2904_);
v_k_2919_ = v___f_2979_;
goto v___jp_2918_;
}
default: 
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v_fvars_2905_);
lean_dec_ref(v_e_2904_);
v___x_2980_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2981_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2980_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
return v___x_2981_;
}
}
v___jp_2918_:
{
if (v_descend_2903_ == 0)
{
lean_object* v___x_2920_; 
lean_dec_ref(v_k_2919_);
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_e_2904_);
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; 
lean_dec_ref(v_e_2904_);
lean_inc(v___y_2916_);
lean_inc_ref(v___y_2915_);
lean_inc(v___y_2914_);
lean_inc_ref(v___y_2913_);
lean_inc(v___y_2912_);
lean_inc(v___y_2911_);
lean_inc_ref(v___y_2910_);
v___x_2921_ = lean_apply_8(v_k_2919_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, lean_box(0));
return v___x_2921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2982_, lean_object* v_e_2983_, lean_object* v_fvars_2984_, lean_object* v___x_2985_, lean_object* v_topLevel_2986_, lean_object* v___y_2987_, lean_object* v_____r_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
uint8_t v_descend_boxed_2997_; uint8_t v___x_51576__boxed_2998_; uint8_t v_topLevel_boxed_2999_; uint8_t v___y_51577__boxed_3000_; lean_object* v_res_3001_; 
v_descend_boxed_2997_ = lean_unbox(v_descend_2982_);
v___x_51576__boxed_2998_ = lean_unbox(v___x_2985_);
v_topLevel_boxed_2999_ = lean_unbox(v_topLevel_2986_);
v___y_51577__boxed_3000_ = lean_unbox(v___y_2987_);
v_res_3001_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2997_, v_e_2983_, v_fvars_2984_, v___x_51576__boxed_2998_, v_topLevel_boxed_2999_, v___y_51577__boxed_3000_, v_____r_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_3002_, lean_object* v_e_3003_, uint8_t v_topLevel_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v___y_3014_; lean_object* v_a_3015_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3025_; lean_object* v___y_3026_; uint8_t v___x_3029_; 
v___x_3029_ = l_Lean_Expr_isAtomic(v_e_3003_);
if (v___x_3029_ == 0)
{
uint8_t v_proofs_3030_; uint8_t v_types_3031_; uint8_t v_descend_3032_; lean_object* v___y_3034_; lean_object* v___y_3035_; uint8_t v___y_3052_; 
v_proofs_3030_ = lean_ctor_get_uint8(v_a_3005_, 0);
v_types_3031_ = lean_ctor_get_uint8(v_a_3005_, 1);
v_descend_3032_ = lean_ctor_get_uint8(v_a_3005_, 3);
if (v_descend_3032_ == 0)
{
goto v___jp_3075_;
}
else
{
if (v___x_3029_ == 0)
{
v___y_3052_ = v___x_3029_;
goto v___jp_3051_;
}
else
{
goto v___jp_3075_;
}
}
v___jp_3033_:
{
if (v_proofs_3030_ == 0)
{
lean_object* v___x_3036_; 
lean_inc_ref(v_e_3003_);
v___x_3036_ = l_Lean_Meta_isProof(v_e_3003_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; uint8_t v___x_3038_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref(v___x_3036_);
v___x_3038_ = lean_unbox(v_a_3037_);
lean_dec(v_a_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec_ref(v_e_3003_);
v___x_3039_ = lean_box(0);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
v___x_3040_ = lean_apply_9(v___y_3034_, v___x_3039_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, lean_box(0));
v___y_3021_ = v___y_3035_;
v___y_3022_ = v___x_3040_;
goto v___jp_3020_;
}
else
{
lean_dec_ref(v___y_3034_);
v___y_3014_ = v___y_3035_;
v_a_3015_ = v_e_3003_;
goto v___jp_3013_;
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v_e_3003_);
v_a_3041_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3036_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3036_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec_ref(v_e_3003_);
v___x_3049_ = lean_box(0);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
v___x_3050_ = lean_apply_9(v___y_3034_, v___x_3049_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, lean_box(0));
v___y_3021_ = v___y_3035_;
v___y_3022_ = v___x_3050_;
goto v___jp_3020_;
}
}
v___jp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = lean_st_ref_get(v_a_3006_);
v___x_3054_ = lean_box(v_topLevel_3004_);
lean_inc_ref(v_e_3003_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v_e_3003_);
v___x_3056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3053_, v___x_3055_);
lean_dec(v___x_3053_);
if (lean_obj_tag(v___x_3056_) == 0)
{
uint8_t v___x_3057_; 
v___x_3057_ = l_Lean_Meta_ExtractLets_containsLet(v_e_3003_);
if (v___x_3057_ == 0)
{
lean_dec(v_fvars_3002_);
v___y_3014_ = v___x_3055_;
v_a_3015_ = v_e_3003_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___f_3064_; 
v___x_3058_ = lean_box(v_descend_3032_);
v___x_3059_ = lean_box(v___x_3057_);
v___x_3060_ = lean_box(v_topLevel_3004_);
v___x_3061_ = lean_box(v___y_3052_);
lean_inc_ref_n(v_e_3003_, 2);
v___f_3062_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3062_, 0, v___x_3058_);
lean_closure_set(v___f_3062_, 1, v_e_3003_);
lean_closure_set(v___f_3062_, 2, v_fvars_3002_);
lean_closure_set(v___f_3062_, 3, v___x_3059_);
lean_closure_set(v___f_3062_, 4, v___x_3060_);
lean_closure_set(v___f_3062_, 5, v___x_3061_);
v___x_3063_ = lean_box(v_types_3031_);
lean_inc_ref(v___f_3062_);
v___f_3064_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3064_, 0, v___x_3063_);
lean_closure_set(v___f_3064_, 1, v_e_3003_);
lean_closure_set(v___f_3064_, 2, v___f_3062_);
if (v_topLevel_3004_ == 0)
{
lean_dec_ref(v___f_3062_);
v___y_3034_ = v___f_3064_;
v___y_3035_ = v___x_3055_;
goto v___jp_3033_;
}
else
{
uint8_t v___x_3065_; 
v___x_3065_ = l_Lean_Expr_isLet(v_e_3003_);
if (v___x_3065_ == 0)
{
uint8_t v___x_3066_; 
v___x_3066_ = l_Lean_Expr_isMData(v_e_3003_);
if (v___x_3066_ == 0)
{
lean_dec_ref(v___f_3062_);
v___y_3034_ = v___f_3064_;
v___y_3035_ = v___x_3055_;
goto v___jp_3033_;
}
else
{
lean_dec_ref(v___f_3064_);
lean_dec_ref(v_e_3003_);
v___y_3025_ = v___f_3062_;
v___y_3026_ = v___x_3055_;
goto v___jp_3024_;
}
}
else
{
lean_dec_ref(v___f_3064_);
lean_dec_ref(v_e_3003_);
v___y_3025_ = v___f_3062_;
v___y_3026_ = v___x_3055_;
goto v___jp_3024_;
}
}
}
}
else
{
lean_object* v_val_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___x_3055_);
lean_dec_ref(v_e_3003_);
lean_dec(v_fvars_3002_);
v_val_3067_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3056_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_val_3067_);
lean_dec(v___x_3056_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 0);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_val_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
v___jp_3075_:
{
if (v_topLevel_3004_ == 0)
{
lean_object* v___x_3076_; 
lean_dec(v_fvars_3002_);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_e_3003_);
return v___x_3076_;
}
else
{
if (v___x_3029_ == 0)
{
v___y_3052_ = v___x_3029_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3077_; 
lean_dec(v_fvars_3002_);
v___x_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3077_, 0, v_e_3003_);
return v___x_3077_;
}
}
}
}
else
{
lean_object* v___x_3078_; 
lean_dec(v_fvars_3002_);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_e_3003_);
return v___x_3078_;
}
v___jp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = lean_st_ref_take(v_a_3006_);
lean_inc_ref(v_a_3015_);
v___x_3017_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3016_, v___y_3014_, v_a_3015_);
v___x_3018_ = lean_st_ref_set(v_a_3006_, v___x_3017_);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_a_3015_);
return v___x_3019_;
}
v___jp_3020_:
{
if (lean_obj_tag(v___y_3022_) == 0)
{
lean_object* v_a_3023_; 
v_a_3023_ = lean_ctor_get(v___y_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref(v___y_3022_);
v___y_3014_ = v___y_3021_;
v_a_3015_ = v_a_3023_;
goto v___jp_3013_;
}
else
{
lean_dec_ref(v___y_3021_);
return v___y_3022_;
}
}
v___jp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_box(0);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
v___x_3028_ = lean_apply_9(v___y_3025_, v___x_3027_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, lean_box(0));
v___y_3021_ = v___y_3026_;
v___y_3022_ = v___x_3028_;
goto v___jp_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3079_, lean_object* v_struct_3080_, uint8_t v___y_3081_, lean_object* v_typeName_3082_, lean_object* v_idx_3083_, lean_object* v_e_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; 
lean_inc_ref(v_struct_3080_);
v___x_3093_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3079_, v_struct_3080_, v___y_3081_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3108_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3108_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3108_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
size_t v___x_3098_; size_t v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = lean_ptr_addr(v_struct_3080_);
lean_dec_ref(v_struct_3080_);
v___x_3099_ = lean_ptr_addr(v_a_3094_);
v___x_3100_ = lean_usize_dec_eq(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_dec_ref(v_e_3084_);
v___x_3101_ = l_Lean_Expr_proj___override(v_typeName_3082_, v_idx_3083_, v_a_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3101_);
v___x_3103_ = v___x_3096_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
lean_object* v___x_3106_; 
lean_dec(v_a_3094_);
lean_dec(v_idx_3083_);
lean_dec(v_typeName_3082_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v_e_3084_);
v___x_3106_ = v___x_3096_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_e_3084_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_dec_ref(v_e_3084_);
lean_dec(v_idx_3083_);
lean_dec(v_typeName_3082_);
lean_dec_ref(v_struct_3080_);
return v___x_3093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3109_, lean_object* v_sz_3110_, lean_object* v_i_3111_, lean_object* v_bs_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
size_t v_sz_boxed_3121_; size_t v_i_boxed_3122_; lean_object* v_res_3123_; 
v_sz_boxed_3121_ = lean_unbox_usize(v_sz_3110_);
lean_dec(v_sz_3110_);
v_i_boxed_3122_ = lean_unbox_usize(v_i_3111_);
lean_dec(v_i_3111_);
v_res_3123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3109_, v_sz_boxed_3121_, v_i_boxed_3122_, v_bs_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3124_, lean_object* v_fst_3125_, lean_object* v_fvars_3126_, lean_object* v_a_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3124_, v_fst_3125_, v_fvars_3126_, v_a_3127_, v_b_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v_fst_3125_);
lean_dec(v_upperBound_3124_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3138_, lean_object* v_e_3139_, lean_object* v_isLet_3140_, lean_object* v_n_3141_, lean_object* v_t_3142_, lean_object* v_v_3143_, lean_object* v_b_3144_, lean_object* v_topLevel_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_){
_start:
{
uint8_t v_isLet_boxed_3154_; uint8_t v_topLevel_boxed_3155_; lean_object* v_res_3156_; 
v_isLet_boxed_3154_ = lean_unbox(v_isLet_3140_);
v_topLevel_boxed_3155_ = lean_unbox(v_topLevel_3145_);
v_res_3156_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3138_, v_e_3139_, v_isLet_boxed_3154_, v_n_3141_, v_t_3142_, v_v_3143_, v_b_3144_, v_topLevel_boxed_3155_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3157_, lean_object* v_name_3158_, lean_object* v_type_3159_, lean_object* v_val_3160_, lean_object* v_k_3161_, uint8_t v_nondep_3162_, uint8_t v_kind_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3158_, v_type_3159_, v_val_3160_, v_k_3161_, v_nondep_3162_, v_kind_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_name_3174_, lean_object* v_type_3175_, lean_object* v_val_3176_, lean_object* v_k_3177_, lean_object* v_nondep_3178_, lean_object* v_kind_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
uint8_t v_nondep_boxed_3188_; uint8_t v_kind_boxed_3189_; lean_object* v_res_3190_; 
v_nondep_boxed_3188_ = lean_unbox(v_nondep_3178_);
v_kind_boxed_3189_ = lean_unbox(v_kind_3179_);
v_res_3190_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3173_, v_name_3174_, v_type_3175_, v_val_3176_, v_k_3177_, v_nondep_boxed_3188_, v_kind_boxed_3189_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3191_, lean_object* v_m_3192_, lean_object* v_a_3193_, lean_object* v_b_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3192_, v_a_3193_, v_b_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3196_, lean_object* v_m_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3197_, v_a_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3200_, lean_object* v_m_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3200_, v_m_3201_, v_a_3202_);
lean_dec_ref(v_a_3202_);
lean_dec_ref(v_m_3201_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3204_, lean_object* v_fst_3205_, lean_object* v_fvars_3206_, lean_object* v_inst_3207_, lean_object* v_R_3208_, lean_object* v_a_3209_, lean_object* v_b_3210_, lean_object* v_c_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3204_, v_fst_3205_, v_fvars_3206_, v_a_3209_, v_b_3210_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3221_, lean_object* v_fst_3222_, lean_object* v_fvars_3223_, lean_object* v_inst_3224_, lean_object* v_R_3225_, lean_object* v_a_3226_, lean_object* v_b_3227_, lean_object* v_c_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3221_, v_fst_3222_, v_fvars_3223_, v_inst_3224_, v_R_3225_, v_a_3226_, v_b_3227_, v_c_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v_fst_3222_);
lean_dec(v_upperBound_3221_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3238_, lean_object* v_m_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3239_, v_a_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3242_, lean_object* v_m_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3242_, v_m_3243_, v_a_3244_);
lean_dec_ref(v_a_3244_);
lean_dec_ref(v_m_3243_);
return v_res_3245_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3246_, lean_object* v_a_3247_, lean_object* v_x_3248_){
_start:
{
uint8_t v___x_3249_; 
v___x_3249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3247_, v_x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3250_, lean_object* v_a_3251_, lean_object* v_x_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3250_, v_a_3251_, v_x_3252_);
lean_dec(v_x_3252_);
lean_dec_ref(v_a_3251_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3255_, lean_object* v_data_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3258_, lean_object* v_a_3259_, lean_object* v_b_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3259_, v_b_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3263_, lean_object* v_a_3264_, lean_object* v_x_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3264_, v_x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3267_, lean_object* v_a_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3267_, v_a_3268_, v_x_3269_);
lean_dec(v_x_3269_);
lean_dec_ref(v_a_3268_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3271_, lean_object* v_a_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3272_, v_x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3275_, lean_object* v_a_3276_, lean_object* v_x_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3275_, v_a_3276_, v_x_3277_);
lean_dec(v_x_3277_);
lean_dec_ref(v_a_3276_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3279_, lean_object* v_i_3280_, lean_object* v_source_3281_, lean_object* v_target_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3280_, v_source_3281_, v_target_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3285_, v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v___x_3297_; lean_object* v_a_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; 
v___x_3297_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3288_, v_a_3293_);
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = lean_box(0);
v___x_3300_ = 1;
v___x_3301_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3299_, v_a_3298_, v___x_3300_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3312_, size_t v_i_3313_, lean_object* v_bs_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_usize_dec_lt(v_i_3313_, v_sz_3312_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v_bs_3314_);
return v___x_3324_;
}
else
{
lean_object* v_v_3325_; lean_object* v___x_3326_; 
v_v_3325_ = lean_array_uget_borrowed(v_bs_3314_, v_i_3313_);
lean_inc(v_v_3325_);
v___x_3326_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3325_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v_bs_x27_3329_; size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v_bs_x27_3329_ = lean_array_uset(v_bs_3314_, v_i_3313_, v___x_3328_);
v___x_3330_ = ((size_t)1ULL);
v___x_3331_ = lean_usize_add(v_i_3313_, v___x_3330_);
v___x_3332_ = lean_array_uset(v_bs_x27_3329_, v_i_3313_, v_a_3327_);
v_i_3313_ = v___x_3331_;
v_bs_3314_ = v___x_3332_;
goto _start;
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec_ref(v_bs_3314_);
v_a_3334_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3326_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3326_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3342_, lean_object* v_i_3343_, lean_object* v_bs_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
size_t v_sz_boxed_3353_; size_t v_i_boxed_3354_; lean_object* v_res_3355_; 
v_sz_boxed_3353_ = lean_unbox_usize(v_sz_3342_);
lean_dec(v_sz_3342_);
v_i_boxed_3354_ = lean_unbox_usize(v_i_3343_);
lean_dec(v_i_3343_);
v_res_3355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3353_, v_i_boxed_3354_, v_bs_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v_merge_3376_; 
v_merge_3376_ = lean_ctor_get_uint8(v_a_3357_, 6);
if (v_merge_3376_ == 0)
{
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
v___y_3369_ = v_a_3360_;
v___y_3370_ = v_a_3361_;
v___y_3371_ = v_a_3362_;
v___y_3372_ = v_a_3363_;
goto v___jp_3365_;
}
else
{
uint8_t v_useContext_3377_; 
v_useContext_3377_ = lean_ctor_get_uint8(v_a_3357_, 7);
if (v_useContext_3377_ == 0)
{
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
v___y_3369_ = v_a_3360_;
v___y_3370_ = v_a_3361_;
v___y_3371_ = v_a_3362_;
v___y_3372_ = v_a_3363_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_dec_ref(v___x_3378_);
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
v___y_3369_ = v_a_3360_;
v___y_3370_ = v_a_3361_;
v___y_3371_ = v_a_3362_;
v___y_3372_ = v_a_3363_;
goto v___jp_3365_;
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec_ref(v_es_3356_);
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
v___jp_3365_:
{
size_t v_sz_3373_; size_t v___x_3374_; lean_object* v___x_3375_; 
v_sz_3373_ = lean_array_size(v_es_3356_);
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3373_, v___x_3374_, v_es_3356_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Meta_ExtractLets_extract(v_es_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3397_, v_x_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
v_a_3413_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3404_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3404_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3421_, lean_object* v_x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3421_, v_x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3429_, lean_object* v_decls_3430_, lean_object* v_x_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3430_, v_x_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3438_, lean_object* v_decls_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3438_, v_decls_3439_, v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3447_, size_t v_i_3448_, lean_object* v_bs_3449_){
_start:
{
uint8_t v___x_3450_; 
v___x_3450_ = lean_usize_dec_lt(v_i_3448_, v_sz_3447_);
if (v___x_3450_ == 0)
{
return v_bs_3449_;
}
else
{
lean_object* v_v_3451_; lean_object* v___x_3452_; lean_object* v_bs_x27_3453_; lean_object* v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v_v_3451_ = lean_array_uget(v_bs_3449_, v_i_3448_);
v___x_3452_ = lean_unsigned_to_nat(0u);
v_bs_x27_3453_ = lean_array_uset(v_bs_3449_, v_i_3448_, v___x_3452_);
v___x_3454_ = l_Lean_LocalDecl_fvarId(v_v_3451_);
lean_dec(v_v_3451_);
v___x_3455_ = ((size_t)1ULL);
v___x_3456_ = lean_usize_add(v_i_3448_, v___x_3455_);
v___x_3457_ = lean_array_uset(v_bs_x27_3453_, v_i_3448_, v___x_3454_);
v_i_3448_ = v___x_3456_;
v_bs_3449_ = v___x_3457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3459_, lean_object* v_i_3460_, lean_object* v_bs_3461_){
_start:
{
size_t v_sz_boxed_3462_; size_t v_i_boxed_3463_; lean_object* v_res_3464_; 
v_sz_boxed_3462_ = lean_unbox_usize(v_sz_3459_);
lean_dec(v_sz_3459_);
v_i_boxed_3463_ = lean_unbox_usize(v_i_3460_);
lean_dec(v_i_3460_);
v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3462_, v_i_boxed_3463_, v_bs_3461_);
return v_res_3464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = lean_box(0);
v___x_3466_ = lean_unsigned_to_nat(16u);
v___x_3467_ = lean_mk_array(v___x_3466_, v___x_3465_);
return v___x_3467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___x_3468_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3471_, lean_object* v_givenNames_3472_, lean_object* v_k_3473_, lean_object* v_config_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3481_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_3482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3482_, 0, v_givenNames_3472_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
lean_ctor_set(v___x_3482_, 2, v___x_3480_);
v___x_3483_ = lean_st_mk_ref(v___x_3482_);
v___x_3484_ = lean_st_mk_ref(v___x_3480_);
v___x_3485_ = l_Lean_Meta_ExtractLets_extract(v_es_3471_, v_config_3474_, v___x_3484_, v___x_3483_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v_givenNames_3489_; lean_object* v_decls_3490_; size_t v_sz_3491_; size_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; size_t v_sz_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v___x_3485_);
v___x_3487_ = lean_st_ref_get(v___x_3484_);
lean_dec(v___x_3484_);
lean_dec(v___x_3487_);
v___x_3488_ = lean_st_ref_get(v___x_3483_);
lean_dec(v___x_3483_);
v_givenNames_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_givenNames_3489_);
v_decls_3490_ = lean_ctor_get(v___x_3488_, 1);
lean_inc_ref(v_decls_3490_);
lean_dec(v___x_3488_);
v_sz_3491_ = lean_array_size(v_decls_3490_);
v___x_3492_ = ((size_t)0ULL);
v___x_3493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_3491_, v___x_3492_, v_decls_3490_);
lean_inc_ref(v___x_3493_);
v___x_3494_ = lean_array_to_list(v___x_3493_);
v_sz_3495_ = lean_array_size(v___x_3493_);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3495_, v___x_3492_, v___x_3493_);
v___x_3497_ = lean_apply_3(v_k_3473_, v___x_3496_, v_a_3486_, v_givenNames_3489_);
v___x_3498_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3494_, v___x_3497_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
return v___x_3498_;
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v___x_3484_);
lean_dec(v___x_3483_);
lean_dec_ref(v_k_3473_);
v_a_3499_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3485_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3485_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3507_, lean_object* v_givenNames_3508_, lean_object* v_k_3509_, lean_object* v_config_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3507_, v_givenNames_3508_, v_k_3509_, v_config_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec_ref(v_config_3510_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3517_, lean_object* v_es_3518_, lean_object* v_givenNames_3519_, lean_object* v_k_3520_, lean_object* v_config_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3518_, v_givenNames_3519_, v_k_3520_, v_config_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3528_, lean_object* v_es_3529_, lean_object* v_givenNames_3530_, lean_object* v_k_3531_, lean_object* v_config_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3528_, v_es_3529_, v_givenNames_3530_, v_k_3531_, v_config_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec_ref(v_config_3532_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3539_, lean_object* v_runInBase_3540_, lean_object* v_b_3541_, lean_object* v_c_3542_, lean_object* v_d_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_apply_3(v_k_3539_, v_b_3541_, v_c_3542_, v_d_3543_);
lean_inc(v___y_3547_);
lean_inc_ref(v___y_3546_);
lean_inc(v___y_3545_);
lean_inc_ref(v___y_3544_);
v___x_3550_ = lean_apply_7(v_runInBase_3540_, lean_box(0), v___x_3549_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, lean_box(0));
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3551_, lean_object* v_runInBase_3552_, lean_object* v_b_3553_, lean_object* v_c_3554_, lean_object* v_d_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3551_, v_runInBase_3552_, v_b_3553_, v_c_3554_, v_d_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3562_, lean_object* v_es_3563_, lean_object* v_givenNames_3564_, lean_object* v_config_3565_, lean_object* v_runInBase_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v___f_3572_; lean_object* v___x_3573_; 
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3572_, 0, v_k_3562_);
lean_closure_set(v___f_3572_, 1, v_runInBase_3566_);
v___x_3573_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3563_, v_givenNames_3564_, v___f_3572_, v_config_3565_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3574_, lean_object* v_es_3575_, lean_object* v_givenNames_3576_, lean_object* v_config_3577_, lean_object* v_runInBase_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3574_, v_es_3575_, v_givenNames_3576_, v_config_3577_, v_runInBase_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_config_3577_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_es_3587_, lean_object* v_givenNames_3588_, lean_object* v_k_3589_, lean_object* v_config_3590_){
_start:
{
lean_object* v_toBind_3591_; lean_object* v_liftWith_3592_; lean_object* v_restoreM_3593_; lean_object* v___f_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_toBind_3591_ = lean_ctor_get(v_inst_3585_, 1);
lean_inc(v_toBind_3591_);
lean_dec_ref(v_inst_3585_);
v_liftWith_3592_ = lean_ctor_get(v_inst_3586_, 0);
lean_inc(v_liftWith_3592_);
v_restoreM_3593_ = lean_ctor_get(v_inst_3586_, 1);
lean_inc(v_restoreM_3593_);
lean_dec_ref(v_inst_3586_);
v___f_3594_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3594_, 0, v_k_3589_);
lean_closure_set(v___f_3594_, 1, v_es_3587_);
lean_closure_set(v___f_3594_, 2, v_givenNames_3588_);
lean_closure_set(v___f_3594_, 3, v_config_3590_);
v___x_3595_ = lean_apply_2(v_liftWith_3592_, lean_box(0), v___f_3594_);
v___x_3596_ = lean_apply_1(v_restoreM_3593_, lean_box(0));
v___x_3597_ = lean_apply_4(v_toBind_3591_, lean_box(0), lean_box(0), v___x_3595_, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3598_, lean_object* v_00_u03b1_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_es_3602_, lean_object* v_givenNames_3603_, lean_object* v_k_3604_, lean_object* v_config_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_Meta_extractLets___redArg(v_inst_3600_, v_inst_3601_, v_es_3602_, v_givenNames_3603_, v_k_3604_, v_config_3605_);
return v___x_3606_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3608_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_3609_ = lean_box(0);
v___x_3610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v___x_3608_);
lean_ctor_set(v___x_3610_, 2, v___x_3607_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3611_, lean_object* v_config_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; uint8_t v_proofs_3623_; uint8_t v_types_3624_; uint8_t v_implicits_3625_; uint8_t v_descend_3626_; uint8_t v_underBinder_3627_; uint8_t v_usedOnly_3628_; uint8_t v_merge_3629_; uint8_t v_useContext_3630_; uint8_t v_preserveBinderNames_3631_; uint8_t v_lift_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3666_; 
v___x_3618_ = lean_unsigned_to_nat(0u);
v___x_3619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3620_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3621_ = lean_st_mk_ref(v___x_3620_);
v___x_3622_ = lean_st_mk_ref(v___x_3619_);
v_proofs_3623_ = lean_ctor_get_uint8(v_config_3612_, 0);
v_types_3624_ = lean_ctor_get_uint8(v_config_3612_, 1);
v_implicits_3625_ = lean_ctor_get_uint8(v_config_3612_, 2);
v_descend_3626_ = lean_ctor_get_uint8(v_config_3612_, 3);
v_underBinder_3627_ = lean_ctor_get_uint8(v_config_3612_, 4);
v_usedOnly_3628_ = lean_ctor_get_uint8(v_config_3612_, 5);
v_merge_3629_ = lean_ctor_get_uint8(v_config_3612_, 6);
v_useContext_3630_ = lean_ctor_get_uint8(v_config_3612_, 7);
v_preserveBinderNames_3631_ = lean_ctor_get_uint8(v_config_3612_, 9);
v_lift_3632_ = lean_ctor_get_uint8(v_config_3612_, 10);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_config_3612_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3634_ = v_config_3612_;
v_isShared_3635_ = v_isSharedCheck_3666_;
goto v_resetjp_3633_;
}
else
{
lean_dec(v_config_3612_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3666_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; lean_object* v___x_3641_; 
v___x_3636_ = lean_unsigned_to_nat(1u);
v___x_3637_ = lean_mk_empty_array_with_capacity(v___x_3636_);
v___x_3638_ = lean_array_push(v___x_3637_, v_e_3611_);
v___x_3639_ = 1;
if (v_isShared_3635_ == 0)
{
v___x_3641_ = v___x_3634_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 0, v_proofs_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 1, v_types_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 2, v_implicits_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 3, v_descend_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 4, v_underBinder_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 5, v_usedOnly_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 6, v_merge_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 7, v_useContext_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 9, v_preserveBinderNames_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 10, v_lift_3632_);
v___x_3641_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; 
lean_ctor_set_uint8(v___x_3641_, 8, v___x_3639_);
v___x_3642_ = l_Lean_Meta_ExtractLets_extract(v___x_3638_, v___x_3641_, v___x_3622_, v___x_3621_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
lean_dec_ref(v___x_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3656_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3656_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3656_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v_decls_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3647_ = lean_st_ref_get(v___x_3622_);
lean_dec(v___x_3622_);
lean_dec(v___x_3647_);
v___x_3648_ = lean_st_ref_get(v___x_3621_);
lean_dec(v___x_3621_);
v_decls_3649_ = lean_ctor_get(v___x_3648_, 1);
lean_inc_ref(v_decls_3649_);
lean_dec(v___x_3648_);
v___x_3650_ = l_Lean_instInhabitedExpr;
v___x_3651_ = lean_array_get(v___x_3650_, v_a_3643_, v___x_3618_);
lean_dec(v_a_3643_);
v___x_3652_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3649_, v___x_3651_);
lean_dec_ref(v_decls_3649_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3652_);
v___x_3654_ = v___x_3645_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec(v___x_3622_);
lean_dec(v___x_3621_);
v_a_3657_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3642_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3642_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3667_, lean_object* v_config_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_Meta_liftLets(v_e_3667_, v_config_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
return v_res_3674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3677_ = l_Lean_stringToMessageData(v___x_3676_);
return v___x_3677_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3680_, lean_object* v_mvarId_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3688_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3680_, v_mvarId_3681_, v___x_3687_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3689_, lean_object* v_mvarId_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3689_, v_mvarId_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3697_, lean_object* v_tactic_3698_, lean_object* v_mvarId_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3698_, v_mvarId_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3706_, lean_object* v_tactic_3707_, lean_object* v_mvarId_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3706_, v_tactic_3707_, v_mvarId_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3715_, lean_object* v_b_3716_, lean_object* v_c_3717_, lean_object* v_d_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v___x_3724_; 
lean_inc(v___y_3722_);
lean_inc_ref(v___y_3721_);
lean_inc(v___y_3720_);
lean_inc_ref(v___y_3719_);
v___x_3724_ = lean_apply_8(v_k_3715_, v_b_3716_, v_c_3717_, v_d_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, lean_box(0));
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3725_, lean_object* v_b_3726_, lean_object* v_c_3727_, lean_object* v_d_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3725_, v_b_3726_, v_c_3727_, v_d_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3735_, lean_object* v_givenNames_3736_, lean_object* v_k_3737_, lean_object* v_config_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___f_3744_; lean_object* v___x_3745_; 
v___f_3744_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3744_, 0, v_k_3737_);
v___x_3745_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3735_, v_givenNames_3736_, v___f_3744_, v_config_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
v_a_3754_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3745_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3745_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3762_, lean_object* v_givenNames_3763_, lean_object* v_k_3764_, lean_object* v_config_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3762_, v_givenNames_3763_, v_k_3764_, v_config_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec_ref(v_config_3765_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3772_, lean_object* v_es_3773_, lean_object* v_givenNames_3774_, lean_object* v_k_3775_, lean_object* v_config_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3773_, v_givenNames_3774_, v_k_3775_, v_config_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3783_, lean_object* v_es_3784_, lean_object* v_givenNames_3785_, lean_object* v_k_3786_, lean_object* v_config_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3783_, v_es_3784_, v_givenNames_3785_, v_k_3786_, v_config_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v_config_3787_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3794_, lean_object* v_x_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3794_, v_x_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
v_a_3810_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3801_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3801_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3818_, lean_object* v_x_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3818_, v_x_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3826_, lean_object* v_mvarId_3827_, lean_object* v_x_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3827_, v_x_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3835_, lean_object* v_mvarId_3836_, lean_object* v_x_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3835_, v_mvarId_3836_, v_x_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3844_, lean_object* v_x_3845_, lean_object* v_x_3846_, lean_object* v_x_3847_){
_start:
{
lean_object* v_ks_3848_; lean_object* v_vs_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3873_; 
v_ks_3848_ = lean_ctor_get(v_x_3844_, 0);
v_vs_3849_ = lean_ctor_get(v_x_3844_, 1);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_x_3844_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3851_ = v_x_3844_;
v_isShared_3852_ = v_isSharedCheck_3873_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_vs_3849_);
lean_inc(v_ks_3848_);
lean_dec(v_x_3844_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3873_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3853_ = lean_array_get_size(v_ks_3848_);
v___x_3854_ = lean_nat_dec_lt(v_x_3845_, v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
lean_dec(v_x_3845_);
v___x_3855_ = lean_array_push(v_ks_3848_, v_x_3846_);
v___x_3856_ = lean_array_push(v_vs_3849_, v_x_3847_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 1, v___x_3856_);
lean_ctor_set(v___x_3851_, 0, v___x_3855_);
v___x_3858_ = v___x_3851_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3859_, 1, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
else
{
lean_object* v_k_x27_3860_; uint8_t v___x_3861_; 
v_k_x27_3860_ = lean_array_fget_borrowed(v_ks_3848_, v_x_3845_);
v___x_3861_ = l_Lean_instBEqMVarId_beq(v_x_3846_, v_k_x27_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3863_; 
if (v_isShared_3852_ == 0)
{
v___x_3863_ = v___x_3851_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_ks_3848_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_vs_3849_);
v___x_3863_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_unsigned_to_nat(1u);
v___x_3865_ = lean_nat_add(v_x_3845_, v___x_3864_);
lean_dec(v_x_3845_);
v_x_3844_ = v___x_3863_;
v_x_3845_ = v___x_3865_;
goto _start;
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3868_ = lean_array_fset(v_ks_3848_, v_x_3845_, v_x_3846_);
v___x_3869_ = lean_array_fset(v_vs_3849_, v_x_3845_, v_x_3847_);
lean_dec(v_x_3845_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 1, v___x_3869_);
lean_ctor_set(v___x_3851_, 0, v___x_3868_);
v___x_3871_ = v___x_3851_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3874_, lean_object* v_k_3875_, lean_object* v_v_3876_){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3874_, v___x_3877_, v_k_3875_, v_v_3876_);
return v___x_3878_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_3879_; size_t v___x_3880_; size_t v___x_3881_; 
v___x_3879_ = ((size_t)5ULL);
v___x_3880_ = ((size_t)1ULL);
v___x_3881_ = lean_usize_shift_left(v___x_3880_, v___x_3879_);
return v___x_3881_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3882_; size_t v___x_3883_; size_t v___x_3884_; 
v___x_3882_ = ((size_t)1ULL);
v___x_3883_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3884_ = lean_usize_sub(v___x_3883_, v___x_3882_);
return v___x_3884_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3886_, size_t v_x_3887_, size_t v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
if (lean_obj_tag(v_x_3886_) == 0)
{
lean_object* v_es_3891_; size_t v___x_3892_; size_t v___x_3893_; size_t v___x_3894_; size_t v___x_3895_; lean_object* v_j_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v_es_3891_ = lean_ctor_get(v_x_3886_, 0);
v___x_3892_ = ((size_t)5ULL);
v___x_3893_ = ((size_t)1ULL);
v___x_3894_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1);
v___x_3895_ = lean_usize_land(v_x_3887_, v___x_3894_);
v_j_3896_ = lean_usize_to_nat(v___x_3895_);
v___x_3897_ = lean_array_get_size(v_es_3891_);
v___x_3898_ = lean_nat_dec_lt(v_j_3896_, v___x_3897_);
if (v___x_3898_ == 0)
{
lean_dec(v_j_3896_);
lean_dec(v_x_3890_);
lean_dec(v_x_3889_);
return v_x_3886_;
}
else
{
lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3935_; 
lean_inc_ref(v_es_3891_);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_x_3886_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; 
v_unused_3936_ = lean_ctor_get(v_x_3886_, 0);
lean_dec(v_unused_3936_);
v___x_3900_ = v_x_3886_;
v_isShared_3901_ = v_isSharedCheck_3935_;
goto v_resetjp_3899_;
}
else
{
lean_dec(v_x_3886_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3935_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_v_3902_; lean_object* v___x_3903_; lean_object* v_xs_x27_3904_; lean_object* v___y_3906_; 
v_v_3902_ = lean_array_fget(v_es_3891_, v_j_3896_);
v___x_3903_ = lean_box(0);
v_xs_x27_3904_ = lean_array_fset(v_es_3891_, v_j_3896_, v___x_3903_);
switch(lean_obj_tag(v_v_3902_))
{
case 0:
{
lean_object* v_key_3911_; lean_object* v_val_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3922_; 
v_key_3911_ = lean_ctor_get(v_v_3902_, 0);
v_val_3912_ = lean_ctor_get(v_v_3902_, 1);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_v_3902_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3914_ = v_v_3902_;
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_val_3912_);
lean_inc(v_key_3911_);
lean_dec(v_v_3902_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
uint8_t v___x_3916_; 
v___x_3916_ = l_Lean_instBEqMVarId_beq(v_x_3889_, v_key_3911_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_del_object(v___x_3914_);
v___x_3917_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3911_, v_val_3912_, v_x_3889_, v_x_3890_);
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v___y_3906_ = v___x_3918_;
goto v___jp_3905_;
}
else
{
lean_object* v___x_3920_; 
lean_dec(v_val_3912_);
lean_dec(v_key_3911_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 1, v_x_3890_);
lean_ctor_set(v___x_3914_, 0, v_x_3889_);
v___x_3920_ = v___x_3914_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_x_3889_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_x_3890_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
v___y_3906_ = v___x_3920_;
goto v___jp_3905_;
}
}
}
}
case 1:
{
lean_object* v_node_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3933_; 
v_node_3923_ = lean_ctor_get(v_v_3902_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_v_3902_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3925_ = v_v_3902_;
v_isShared_3926_ = v_isSharedCheck_3933_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_node_3923_);
lean_dec(v_v_3902_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3933_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
size_t v___x_3927_; size_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3927_ = lean_usize_shift_right(v_x_3887_, v___x_3892_);
v___x_3928_ = lean_usize_add(v_x_3888_, v___x_3893_);
v___x_3929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3923_, v___x_3927_, v___x_3928_, v_x_3889_, v_x_3890_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3929_);
v___x_3931_ = v___x_3925_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
v___y_3906_ = v___x_3931_;
goto v___jp_3905_;
}
}
}
default: 
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v_x_3889_);
lean_ctor_set(v___x_3934_, 1, v_x_3890_);
v___y_3906_ = v___x_3934_;
goto v___jp_3905_;
}
}
v___jp_3905_:
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3907_ = lean_array_fset(v_xs_x27_3904_, v_j_3896_, v___y_3906_);
lean_dec(v_j_3896_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3907_);
v___x_3909_ = v___x_3900_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
else
{
lean_object* v_ks_3937_; lean_object* v_vs_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3958_; 
v_ks_3937_ = lean_ctor_get(v_x_3886_, 0);
v_vs_3938_ = lean_ctor_get(v_x_3886_, 1);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_x_3886_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3940_ = v_x_3886_;
v_isShared_3941_ = v_isSharedCheck_3958_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_vs_3938_);
lean_inc(v_ks_3937_);
lean_dec(v_x_3886_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3958_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_ks_3937_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_vs_3938_);
v___x_3943_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v_newNode_3944_; uint8_t v___y_3946_; size_t v___x_3952_; uint8_t v___x_3953_; 
v_newNode_3944_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3943_, v_x_3889_, v_x_3890_);
v___x_3952_ = ((size_t)7ULL);
v___x_3953_ = lean_usize_dec_le(v___x_3952_, v_x_3888_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3954_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3944_);
v___x_3955_ = lean_unsigned_to_nat(4u);
v___x_3956_ = lean_nat_dec_lt(v___x_3954_, v___x_3955_);
lean_dec(v___x_3954_);
v___y_3946_ = v___x_3956_;
goto v___jp_3945_;
}
else
{
v___y_3946_ = v___x_3953_;
goto v___jp_3945_;
}
v___jp_3945_:
{
if (v___y_3946_ == 0)
{
lean_object* v_ks_3947_; lean_object* v_vs_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_ks_3947_ = lean_ctor_get(v_newNode_3944_, 0);
lean_inc_ref(v_ks_3947_);
v_vs_3948_ = lean_ctor_get(v_newNode_3944_, 1);
lean_inc_ref(v_vs_3948_);
lean_dec_ref(v_newNode_3944_);
v___x_3949_ = lean_unsigned_to_nat(0u);
v___x_3950_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_3951_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3888_, v_ks_3947_, v_vs_3948_, v___x_3949_, v___x_3950_);
lean_dec_ref(v_vs_3948_);
lean_dec_ref(v_ks_3947_);
return v___x_3951_;
}
else
{
return v_newNode_3944_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3959_, lean_object* v_keys_3960_, lean_object* v_vals_3961_, lean_object* v_i_3962_, lean_object* v_entries_3963_){
_start:
{
lean_object* v___x_3964_; uint8_t v___x_3965_; 
v___x_3964_ = lean_array_get_size(v_keys_3960_);
v___x_3965_ = lean_nat_dec_lt(v_i_3962_, v___x_3964_);
if (v___x_3965_ == 0)
{
lean_dec(v_i_3962_);
return v_entries_3963_;
}
else
{
lean_object* v_k_3966_; lean_object* v_v_3967_; uint64_t v___x_3968_; size_t v_h_3969_; size_t v___x_3970_; lean_object* v___x_3971_; size_t v___x_3972_; size_t v___x_3973_; size_t v___x_3974_; size_t v_h_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_k_3966_ = lean_array_fget_borrowed(v_keys_3960_, v_i_3962_);
v_v_3967_ = lean_array_fget_borrowed(v_vals_3961_, v_i_3962_);
v___x_3968_ = l_Lean_instHashableMVarId_hash(v_k_3966_);
v_h_3969_ = lean_uint64_to_usize(v___x_3968_);
v___x_3970_ = ((size_t)5ULL);
v___x_3971_ = lean_unsigned_to_nat(1u);
v___x_3972_ = ((size_t)1ULL);
v___x_3973_ = lean_usize_sub(v_depth_3959_, v___x_3972_);
v___x_3974_ = lean_usize_mul(v___x_3970_, v___x_3973_);
v_h_3975_ = lean_usize_shift_right(v_h_3969_, v___x_3974_);
v___x_3976_ = lean_nat_add(v_i_3962_, v___x_3971_);
lean_dec(v_i_3962_);
lean_inc(v_v_3967_);
lean_inc(v_k_3966_);
v___x_3977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3963_, v_h_3975_, v_depth_3959_, v_k_3966_, v_v_3967_);
v_i_3962_ = v___x_3976_;
v_entries_3963_ = v___x_3977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3979_, lean_object* v_keys_3980_, lean_object* v_vals_3981_, lean_object* v_i_3982_, lean_object* v_entries_3983_){
_start:
{
size_t v_depth_boxed_3984_; lean_object* v_res_3985_; 
v_depth_boxed_3984_ = lean_unbox_usize(v_depth_3979_);
lean_dec(v_depth_3979_);
v_res_3985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3984_, v_keys_3980_, v_vals_3981_, v_i_3982_, v_entries_3983_);
lean_dec_ref(v_vals_3981_);
lean_dec_ref(v_keys_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3986_, lean_object* v_x_3987_, lean_object* v_x_3988_, lean_object* v_x_3989_, lean_object* v_x_3990_){
_start:
{
size_t v_x_2319__boxed_3991_; size_t v_x_2320__boxed_3992_; lean_object* v_res_3993_; 
v_x_2319__boxed_3991_ = lean_unbox_usize(v_x_3987_);
lean_dec(v_x_3987_);
v_x_2320__boxed_3992_ = lean_unbox_usize(v_x_3988_);
lean_dec(v_x_3988_);
v_res_3993_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3986_, v_x_2319__boxed_3991_, v_x_2320__boxed_3992_, v_x_3989_, v_x_3990_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
uint64_t v___x_3997_; size_t v___x_3998_; size_t v___x_3999_; lean_object* v___x_4000_; 
v___x_3997_ = l_Lean_instHashableMVarId_hash(v_x_3995_);
v___x_3998_ = lean_uint64_to_usize(v___x_3997_);
v___x_3999_ = ((size_t)1ULL);
v___x_4000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3994_, v___x_3998_, v___x_3999_, v_x_3995_, v_x_3996_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_4001_, lean_object* v_val_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; lean_object* v_mctx_4006_; lean_object* v_cache_4007_; lean_object* v_zetaDeltaFVarIds_4008_; lean_object* v_postponed_4009_; lean_object* v_diag_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4037_; 
v___x_4005_ = lean_st_ref_take(v___y_4003_);
v_mctx_4006_ = lean_ctor_get(v___x_4005_, 0);
v_cache_4007_ = lean_ctor_get(v___x_4005_, 1);
v_zetaDeltaFVarIds_4008_ = lean_ctor_get(v___x_4005_, 2);
v_postponed_4009_ = lean_ctor_get(v___x_4005_, 3);
v_diag_4010_ = lean_ctor_get(v___x_4005_, 4);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4012_ = v___x_4005_;
v_isShared_4013_ = v_isSharedCheck_4037_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_diag_4010_);
lean_inc(v_postponed_4009_);
lean_inc(v_zetaDeltaFVarIds_4008_);
lean_inc(v_cache_4007_);
lean_inc(v_mctx_4006_);
lean_dec(v___x_4005_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4037_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_depth_4014_; lean_object* v_levelAssignDepth_4015_; lean_object* v_mvarCounter_4016_; lean_object* v_lDepth_4017_; lean_object* v_decls_4018_; lean_object* v_userNames_4019_; lean_object* v_lAssignment_4020_; lean_object* v_eAssignment_4021_; lean_object* v_dAssignment_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4036_; 
v_depth_4014_ = lean_ctor_get(v_mctx_4006_, 0);
v_levelAssignDepth_4015_ = lean_ctor_get(v_mctx_4006_, 1);
v_mvarCounter_4016_ = lean_ctor_get(v_mctx_4006_, 2);
v_lDepth_4017_ = lean_ctor_get(v_mctx_4006_, 3);
v_decls_4018_ = lean_ctor_get(v_mctx_4006_, 4);
v_userNames_4019_ = lean_ctor_get(v_mctx_4006_, 5);
v_lAssignment_4020_ = lean_ctor_get(v_mctx_4006_, 6);
v_eAssignment_4021_ = lean_ctor_get(v_mctx_4006_, 7);
v_dAssignment_4022_ = lean_ctor_get(v_mctx_4006_, 8);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_mctx_4006_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4024_ = v_mctx_4006_;
v_isShared_4025_ = v_isSharedCheck_4036_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_dAssignment_4022_);
lean_inc(v_eAssignment_4021_);
lean_inc(v_lAssignment_4020_);
lean_inc(v_userNames_4019_);
lean_inc(v_decls_4018_);
lean_inc(v_lDepth_4017_);
lean_inc(v_mvarCounter_4016_);
lean_inc(v_levelAssignDepth_4015_);
lean_inc(v_depth_4014_);
lean_dec(v_mctx_4006_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4036_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4026_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_4021_, v_mvarId_4001_, v_val_4002_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 7, v___x_4026_);
v___x_4028_ = v___x_4024_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_depth_4014_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_levelAssignDepth_4015_);
lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_mvarCounter_4016_);
lean_ctor_set(v_reuseFailAlloc_4035_, 3, v_lDepth_4017_);
lean_ctor_set(v_reuseFailAlloc_4035_, 4, v_decls_4018_);
lean_ctor_set(v_reuseFailAlloc_4035_, 5, v_userNames_4019_);
lean_ctor_set(v_reuseFailAlloc_4035_, 6, v_lAssignment_4020_);
lean_ctor_set(v_reuseFailAlloc_4035_, 7, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4035_, 8, v_dAssignment_4022_);
v___x_4028_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4028_);
v___x_4030_ = v___x_4012_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_cache_4007_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v_zetaDeltaFVarIds_4008_);
lean_ctor_set(v_reuseFailAlloc_4034_, 3, v_postponed_4009_);
lean_ctor_set(v_reuseFailAlloc_4034_, 4, v_diag_4010_);
v___x_4030_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4031_ = lean_st_ref_set(v___y_4003_, v___x_4030_);
v___x_4032_ = lean_box(0);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4038_, lean_object* v_val_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4038_, v_val_4039_, v___y_4040_);
lean_dec(v___y_4040_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4043_, size_t v_i_4044_, lean_object* v_bs_4045_){
_start:
{
uint8_t v___x_4046_; 
v___x_4046_ = lean_usize_dec_lt(v_i_4044_, v_sz_4043_);
if (v___x_4046_ == 0)
{
return v_bs_4045_;
}
else
{
lean_object* v_v_4047_; lean_object* v___x_4048_; lean_object* v_bs_x27_4049_; lean_object* v___x_4050_; size_t v___x_4051_; size_t v___x_4052_; lean_object* v___x_4053_; 
v_v_4047_ = lean_array_uget(v_bs_4045_, v_i_4044_);
v___x_4048_ = lean_unsigned_to_nat(0u);
v_bs_x27_4049_ = lean_array_uset(v_bs_4045_, v_i_4044_, v___x_4048_);
v___x_4050_ = l_Lean_Expr_fvar___override(v_v_4047_);
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_add(v_i_4044_, v___x_4051_);
v___x_4053_ = lean_array_uset(v_bs_x27_4049_, v_i_4044_, v___x_4050_);
v_i_4044_ = v___x_4052_;
v_bs_4045_ = v___x_4053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4055_, lean_object* v_i_4056_, lean_object* v_bs_4057_){
_start:
{
size_t v_sz_boxed_4058_; size_t v_i_boxed_4059_; lean_object* v_res_4060_; 
v_sz_boxed_4058_ = lean_unbox_usize(v_sz_4055_);
lean_dec(v_sz_4055_);
v_i_boxed_4059_ = lean_unbox_usize(v_i_4056_);
lean_dec(v_i_4056_);
v_res_4060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4058_, v_i_boxed_4059_, v_bs_4057_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4061_, lean_object* v_mvarId_4062_, lean_object* v___x_4063_, lean_object* v_a_4064_, lean_object* v_fvarIds_4065_, lean_object* v_es_4066_, lean_object* v_givenNames_x27_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; uint8_t v___y_4125_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
v___x_4073_ = lean_unsigned_to_nat(0u);
v___x_4074_ = lean_array_get_borrowed(v___x_4061_, v_es_4066_, v___x_4073_);
v___x_4135_ = lean_array_get_size(v_fvarIds_4065_);
v___x_4136_ = lean_nat_dec_eq(v___x_4135_, v___x_4073_);
if (v___x_4136_ == 0)
{
v___y_4125_ = v___x_4136_;
goto v___jp_4124_;
}
else
{
uint8_t v___x_4137_; 
v___x_4137_ = lean_expr_eqv(v_a_4064_, v___x_4074_);
v___y_4125_ = v___x_4137_;
goto v___jp_4124_;
}
v___jp_4075_:
{
lean_object* v___x_4076_; 
lean_inc(v_mvarId_4062_);
v___x_4076_ = l_Lean_MVarId_getTag(v_mvarId_4062_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4078_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref(v___x_4076_);
lean_inc(v___x_4074_);
v___x_4078_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4074_, v_a_4077_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; size_t v_sz_4080_; size_t v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; uint8_t v___x_4084_; uint8_t v___x_4085_; lean_object* v___x_4086_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc_n(v_a_4079_, 2);
lean_dec_ref(v___x_4078_);
v_sz_4080_ = lean_array_size(v_fvarIds_4065_);
v___x_4081_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4065_);
v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4080_, v___x_4081_, v_fvarIds_4065_);
v___x_4083_ = 0;
v___x_4084_ = 1;
v___x_4085_ = 1;
v___x_4086_ = l_Lean_Meta_mkLetFVars(v___x_4082_, v_a_4079_, v___x_4083_, v___x_4084_, v___x_4085_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec_ref(v___x_4082_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4098_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref(v___x_4086_);
v___x_4088_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4062_, v_a_4087_, v___y_4069_);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; 
v_unused_4099_ = lean_ctor_get(v___x_4088_, 0);
lean_dec(v_unused_4099_);
v___x_4090_ = v___x_4088_;
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
else
{
lean_dec(v___x_4088_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4096_; 
v___x_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4092_, 0, v_fvarIds_4065_);
lean_ctor_set(v___x_4092_, 1, v_givenNames_x27_4067_);
v___x_4093_ = l_Lean_Expr_mvarId_x21(v_a_4079_);
lean_dec(v_a_4079_);
v___x_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4094_);
v___x_4096_ = v___x_4090_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4094_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_a_4079_);
lean_dec(v_givenNames_x27_4067_);
lean_dec_ref(v_fvarIds_4065_);
lean_dec(v_mvarId_4062_);
v_a_4100_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4086_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4086_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_givenNames_x27_4067_);
lean_dec_ref(v_fvarIds_4065_);
lean_dec(v_mvarId_4062_);
v_a_4108_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4078_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4078_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec(v_givenNames_x27_4067_);
lean_dec_ref(v_fvarIds_4065_);
lean_dec(v_mvarId_4062_);
v_a_4116_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4076_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4076_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
v___jp_4124_:
{
if (v___y_4125_ == 0)
{
lean_dec(v___x_4063_);
goto v___jp_4075_;
}
else
{
lean_object* v___x_4126_; 
lean_inc(v_mvarId_4062_);
v___x_4126_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4063_, v_mvarId_4062_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_dec_ref(v___x_4126_);
goto v___jp_4075_;
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v_givenNames_x27_4067_);
lean_dec_ref(v_fvarIds_4065_);
lean_dec(v_mvarId_4062_);
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4138_, lean_object* v_mvarId_4139_, lean_object* v___x_4140_, lean_object* v_a_4141_, lean_object* v_fvarIds_4142_, lean_object* v_es_4143_, lean_object* v_givenNames_x27_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_MVarId_extractLets___lam__0(v___x_4138_, v_mvarId_4139_, v___x_4140_, v_a_4141_, v_fvarIds_4142_, v_es_4143_, v_givenNames_x27_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec_ref(v_es_4143_);
lean_dec_ref(v_a_4141_);
lean_dec_ref(v___x_4138_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4151_, lean_object* v___x_4152_, lean_object* v___x_4153_, lean_object* v_givenNames_4154_, lean_object* v_config_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
lean_inc(v___x_4152_);
lean_inc(v_mvarId_4151_);
v___x_4161_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4151_, v___x_4152_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v___x_4162_; 
lean_dec_ref(v___x_4161_);
lean_inc(v_mvarId_4151_);
v___x_4162_ = l_Lean_MVarId_getType(v_mvarId_4151_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___f_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc_n(v_a_4163_, 2);
lean_dec_ref(v___x_4162_);
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4164_, 0, v___x_4153_);
lean_closure_set(v___f_4164_, 1, v_mvarId_4151_);
lean_closure_set(v___f_4164_, 2, v___x_4152_);
lean_closure_set(v___f_4164_, 3, v_a_4163_);
v___x_4165_ = lean_unsigned_to_nat(1u);
v___x_4166_ = lean_mk_empty_array_with_capacity(v___x_4165_);
v___x_4167_ = lean_array_push(v___x_4166_, v_a_4163_);
v___x_4168_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4167_, v_givenNames_4154_, v___f_4164_, v_config_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4168_;
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec(v_givenNames_4154_);
lean_dec_ref(v___x_4153_);
lean_dec(v___x_4152_);
lean_dec(v_mvarId_4151_);
v_a_4169_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4162_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4162_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec(v_givenNames_4154_);
lean_dec_ref(v___x_4153_);
lean_dec(v___x_4152_);
lean_dec(v_mvarId_4151_);
v_a_4177_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4161_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4161_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4185_, lean_object* v___x_4186_, lean_object* v___x_4187_, lean_object* v_givenNames_4188_, lean_object* v_config_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4185_, v___x_4186_, v___x_4187_, v_givenNames_4188_, v_config_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec_ref(v_config_4189_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4199_, lean_object* v_givenNames_4200_, lean_object* v_config_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___f_4209_; lean_object* v___x_4210_; 
v___x_4207_ = l_Lean_instInhabitedExpr;
v___x_4208_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4199_);
v___f_4209_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4209_, 0, v_mvarId_4199_);
lean_closure_set(v___f_4209_, 1, v___x_4208_);
lean_closure_set(v___f_4209_, 2, v___x_4207_);
lean_closure_set(v___f_4209_, 3, v_givenNames_4200_);
lean_closure_set(v___f_4209_, 4, v_config_4201_);
v___x_4210_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4199_, v___f_4209_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4211_, lean_object* v_givenNames_4212_, lean_object* v_config_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_MVarId_extractLets(v_mvarId_4211_, v_givenNames_4212_, v_config_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4220_, lean_object* v_val_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4220_, v_val_4221_, v___y_4223_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4228_, lean_object* v_val_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4228_, v_val_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4236_, lean_object* v_x_4237_, lean_object* v_x_4238_, lean_object* v_x_4239_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4237_, v_x_4238_, v_x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4241_, lean_object* v_x_4242_, size_t v_x_4243_, size_t v_x_4244_, lean_object* v_x_4245_, lean_object* v_x_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4242_, v_x_4243_, v_x_4244_, v_x_4245_, v_x_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4248_, lean_object* v_x_4249_, lean_object* v_x_4250_, lean_object* v_x_4251_, lean_object* v_x_4252_, lean_object* v_x_4253_){
_start:
{
size_t v_x_2823__boxed_4254_; size_t v_x_2824__boxed_4255_; lean_object* v_res_4256_; 
v_x_2823__boxed_4254_ = lean_unbox_usize(v_x_4250_);
lean_dec(v_x_4250_);
v_x_2824__boxed_4255_ = lean_unbox_usize(v_x_4251_);
lean_dec(v_x_4251_);
v_res_4256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4248_, v_x_4249_, v_x_2823__boxed_4254_, v_x_2824__boxed_4255_, v_x_4252_, v_x_4253_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4257_, lean_object* v_n_4258_, lean_object* v_k_4259_, lean_object* v_v_4260_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4258_, v_k_4259_, v_v_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4262_, size_t v_depth_4263_, lean_object* v_keys_4264_, lean_object* v_vals_4265_, lean_object* v_heq_4266_, lean_object* v_i_4267_, lean_object* v_entries_4268_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4263_, v_keys_4264_, v_vals_4265_, v_i_4267_, v_entries_4268_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4270_, lean_object* v_depth_4271_, lean_object* v_keys_4272_, lean_object* v_vals_4273_, lean_object* v_heq_4274_, lean_object* v_i_4275_, lean_object* v_entries_4276_){
_start:
{
size_t v_depth_boxed_4277_; lean_object* v_res_4278_; 
v_depth_boxed_4277_ = lean_unbox_usize(v_depth_4271_);
lean_dec(v_depth_4271_);
v_res_4278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4270_, v_depth_boxed_4277_, v_keys_4272_, v_vals_4273_, v_heq_4274_, v_i_4275_, v_entries_4276_);
lean_dec_ref(v_vals_4273_);
lean_dec_ref(v_keys_4272_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_, lean_object* v_x_4282_, lean_object* v_x_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4280_, v_x_4281_, v_x_4282_, v_x_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4285_, size_t v_i_4286_, lean_object* v_bs_4287_){
_start:
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_usize_dec_lt(v_i_4286_, v_sz_4285_);
if (v___x_4288_ == 0)
{
return v_bs_4287_;
}
else
{
lean_object* v_v_4289_; lean_object* v___x_4290_; lean_object* v_bs_x27_4291_; lean_object* v___x_4292_; size_t v___x_4293_; size_t v___x_4294_; lean_object* v___x_4295_; 
v_v_4289_ = lean_array_uget(v_bs_4287_, v_i_4286_);
v___x_4290_ = lean_unsigned_to_nat(0u);
v_bs_x27_4291_ = lean_array_uset(v_bs_4287_, v_i_4286_, v___x_4290_);
v___x_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4292_, 0, v_v_4289_);
v___x_4293_ = ((size_t)1ULL);
v___x_4294_ = lean_usize_add(v_i_4286_, v___x_4293_);
v___x_4295_ = lean_array_uset(v_bs_x27_4291_, v_i_4286_, v___x_4292_);
v_i_4286_ = v___x_4294_;
v_bs_4287_ = v___x_4295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4297_, lean_object* v_i_4298_, lean_object* v_bs_4299_){
_start:
{
size_t v_sz_boxed_4300_; size_t v_i_boxed_4301_; lean_object* v_res_4302_; 
v_sz_boxed_4300_ = lean_unbox_usize(v_sz_4297_);
lean_dec(v_sz_4297_);
v_i_boxed_4301_ = lean_unbox_usize(v_i_4298_);
lean_dec(v_i_4298_);
v_res_4302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4300_, v_i_boxed_4301_, v_bs_4299_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4303_, lean_object* v_fvars_4304_, lean_object* v_fvarIds_4305_, lean_object* v_givenNames_x27_4306_, lean_object* v_targetNew_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
lean_inc(v_mvarId_4303_);
v___x_4313_ = l_Lean_MVarId_getTag(v_mvarId_4303_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4315_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref(v___x_4313_);
v___x_4315_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4307_, v_a_4314_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; size_t v_sz_4317_; size_t v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; uint8_t v___x_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc_n(v_a_4316_, 2);
lean_dec_ref(v___x_4315_);
v_sz_4317_ = lean_array_size(v_fvarIds_4305_);
v___x_4318_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4305_);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4317_, v___x_4318_, v_fvarIds_4305_);
v___x_4320_ = 0;
v___x_4321_ = 1;
v___x_4322_ = 1;
v___x_4323_ = l_Lean_Meta_mkLetFVars(v___x_4319_, v_a_4316_, v___x_4320_, v___x_4321_, v___x_4322_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec_ref(v___x_4319_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4338_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref(v___x_4323_);
v___x_4325_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4303_, v_a_4324_, v___y_4309_);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4338_ == 0)
{
lean_object* v_unused_4339_; 
v_unused_4339_ = lean_ctor_get(v___x_4325_, 0);
lean_dec(v_unused_4339_);
v___x_4327_ = v___x_4325_;
v_isShared_4328_ = v_isSharedCheck_4338_;
goto v_resetjp_4326_;
}
else
{
lean_dec(v___x_4325_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4338_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; size_t v_sz_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v_fvarIds_4305_);
lean_ctor_set(v___x_4329_, 1, v_givenNames_x27_4306_);
v_sz_4330_ = lean_array_size(v_fvars_4304_);
v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4330_, v___x_4318_, v_fvars_4304_);
v___x_4332_ = l_Lean_Expr_mvarId_x21(v_a_4316_);
lean_dec(v_a_4316_);
v___x_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4331_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4329_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4334_);
v___x_4336_ = v___x_4327_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec(v_a_4316_);
lean_dec(v_givenNames_x27_4306_);
lean_dec_ref(v_fvarIds_4305_);
lean_dec_ref(v_fvars_4304_);
lean_dec(v_mvarId_4303_);
v_a_4340_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4323_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4323_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec(v_givenNames_x27_4306_);
lean_dec_ref(v_fvarIds_4305_);
lean_dec_ref(v_fvars_4304_);
lean_dec(v_mvarId_4303_);
v_a_4348_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4315_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4315_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec_ref(v_targetNew_4307_);
lean_dec(v_givenNames_x27_4306_);
lean_dec_ref(v_fvarIds_4305_);
lean_dec_ref(v_fvars_4304_);
lean_dec(v_mvarId_4303_);
v_a_4356_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4313_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4313_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4364_, lean_object* v_fvars_4365_, lean_object* v_fvarIds_4366_, lean_object* v_givenNames_x27_4367_, lean_object* v_targetNew_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4364_, v_fvars_4365_, v_fvarIds_4366_, v_givenNames_x27_4367_, v_targetNew_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4375_, lean_object* v_binderName_4376_, lean_object* v_body_4377_, uint8_t v_binderInfo_4378_, lean_object* v___f_4379_, lean_object* v___x_4380_, lean_object* v_mvarId_4381_, lean_object* v_binderType_4382_, lean_object* v_fvarIds_4383_, lean_object* v_es_4384_, lean_object* v_givenNames_x27_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___y_4397_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_4391_ = lean_unsigned_to_nat(0u);
v___x_4392_ = lean_array_get_borrowed(v___x_4375_, v_es_4384_, v___x_4391_);
v___x_4407_ = lean_array_get_size(v_fvarIds_4383_);
v___x_4408_ = lean_nat_dec_eq(v___x_4407_, v___x_4391_);
if (v___x_4408_ == 0)
{
v___y_4397_ = v___x_4408_;
goto v___jp_4396_;
}
else
{
uint8_t v___x_4409_; 
v___x_4409_ = lean_expr_eqv(v_binderType_4382_, v___x_4392_);
v___y_4397_ = v___x_4409_;
goto v___jp_4396_;
}
v___jp_4393_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_inc(v___x_4392_);
v___x_4394_ = l_Lean_Expr_forallE___override(v_binderName_4376_, v___x_4392_, v_body_4377_, v_binderInfo_4378_);
lean_inc(v___y_4389_);
lean_inc_ref(v___y_4388_);
lean_inc(v___y_4387_);
lean_inc_ref(v___y_4386_);
v___x_4395_ = lean_apply_8(v___f_4379_, v_fvarIds_4383_, v_givenNames_x27_4385_, v___x_4394_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, lean_box(0));
return v___x_4395_;
}
v___jp_4396_:
{
if (v___y_4397_ == 0)
{
lean_dec(v_mvarId_4381_);
lean_dec(v___x_4380_);
goto v___jp_4393_;
}
else
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4380_, v_mvarId_4381_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_dec_ref(v___x_4398_);
goto v___jp_4393_;
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_givenNames_x27_4385_);
lean_dec_ref(v_fvarIds_4383_);
lean_dec_ref(v___f_4379_);
lean_dec_ref(v_body_4377_);
lean_dec(v_binderName_4376_);
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4398_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4398_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4410_, lean_object* v_binderName_4411_, lean_object* v_body_4412_, lean_object* v_binderInfo_4413_, lean_object* v___f_4414_, lean_object* v___x_4415_, lean_object* v_mvarId_4416_, lean_object* v_binderType_4417_, lean_object* v_fvarIds_4418_, lean_object* v_es_4419_, lean_object* v_givenNames_x27_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
uint8_t v_binderInfo_1852__boxed_4426_; lean_object* v_res_4427_; 
v_binderInfo_1852__boxed_4426_ = lean_unbox(v_binderInfo_4413_);
v_res_4427_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4410_, v_binderName_4411_, v_body_4412_, v_binderInfo_1852__boxed_4426_, v___f_4414_, v___x_4415_, v_mvarId_4416_, v_binderType_4417_, v_fvarIds_4418_, v_es_4419_, v_givenNames_x27_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec_ref(v_es_4419_);
lean_dec_ref(v_binderType_4417_);
lean_dec_ref(v___x_4410_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4428_, lean_object* v_declName_4429_, lean_object* v_body_4430_, uint8_t v_nondep_4431_, lean_object* v___f_4432_, lean_object* v_value_4433_, lean_object* v___x_4434_, lean_object* v_mvarId_4435_, lean_object* v_type_4436_, lean_object* v_fvarIds_4437_, lean_object* v_es_4438_, lean_object* v_givenNames_x27_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___y_4453_; lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4445_ = lean_unsigned_to_nat(0u);
v___x_4446_ = lean_array_get_borrowed(v___x_4428_, v_es_4438_, v___x_4445_);
v___x_4447_ = lean_unsigned_to_nat(1u);
v___x_4448_ = lean_array_get_borrowed(v___x_4428_, v_es_4438_, v___x_4447_);
v___x_4464_ = lean_array_get_size(v_fvarIds_4437_);
v___x_4465_ = lean_nat_dec_eq(v___x_4464_, v___x_4445_);
if (v___x_4465_ == 0)
{
v___y_4453_ = v___x_4465_;
goto v___jp_4452_;
}
else
{
uint8_t v___x_4466_; 
v___x_4466_ = lean_expr_eqv(v_type_4436_, v___x_4446_);
v___y_4453_ = v___x_4466_;
goto v___jp_4452_;
}
v___jp_4449_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_inc(v___x_4448_);
lean_inc(v___x_4446_);
v___x_4450_ = l_Lean_Expr_letE___override(v_declName_4429_, v___x_4446_, v___x_4448_, v_body_4430_, v_nondep_4431_);
lean_inc(v___y_4443_);
lean_inc_ref(v___y_4442_);
lean_inc(v___y_4441_);
lean_inc_ref(v___y_4440_);
v___x_4451_ = lean_apply_8(v___f_4432_, v_fvarIds_4437_, v_givenNames_x27_4439_, v___x_4450_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, lean_box(0));
return v___x_4451_;
}
v___jp_4452_:
{
if (v___y_4453_ == 0)
{
lean_dec(v_mvarId_4435_);
lean_dec(v___x_4434_);
goto v___jp_4449_;
}
else
{
uint8_t v___x_4454_; 
v___x_4454_ = lean_expr_eqv(v_value_4433_, v___x_4448_);
if (v___x_4454_ == 0)
{
lean_dec(v_mvarId_4435_);
lean_dec(v___x_4434_);
goto v___jp_4449_;
}
else
{
lean_object* v___x_4455_; 
v___x_4455_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4434_, v_mvarId_4435_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_dec_ref(v___x_4455_);
goto v___jp_4449_;
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec(v_givenNames_x27_4439_);
lean_dec_ref(v_fvarIds_4437_);
lean_dec_ref(v___f_4432_);
lean_dec_ref(v_body_4430_);
lean_dec(v_declName_4429_);
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4455_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4455_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4467_ = _args[0];
lean_object* v_declName_4468_ = _args[1];
lean_object* v_body_4469_ = _args[2];
lean_object* v_nondep_4470_ = _args[3];
lean_object* v___f_4471_ = _args[4];
lean_object* v_value_4472_ = _args[5];
lean_object* v___x_4473_ = _args[6];
lean_object* v_mvarId_4474_ = _args[7];
lean_object* v_type_4475_ = _args[8];
lean_object* v_fvarIds_4476_ = _args[9];
lean_object* v_es_4477_ = _args[10];
lean_object* v_givenNames_x27_4478_ = _args[11];
lean_object* v___y_4479_ = _args[12];
lean_object* v___y_4480_ = _args[13];
lean_object* v___y_4481_ = _args[14];
lean_object* v___y_4482_ = _args[15];
lean_object* v___y_4483_ = _args[16];
_start:
{
uint8_t v_nondep_1927__boxed_4484_; lean_object* v_res_4485_; 
v_nondep_1927__boxed_4484_ = lean_unbox(v_nondep_4470_);
v_res_4485_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4467_, v_declName_4468_, v_body_4469_, v_nondep_1927__boxed_4484_, v___f_4471_, v_value_4472_, v___x_4473_, v_mvarId_4474_, v_type_4475_, v_fvarIds_4476_, v_es_4477_, v_givenNames_x27_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec_ref(v_es_4477_);
lean_dec_ref(v_type_4475_);
lean_dec_ref(v_value_4472_);
lean_dec_ref(v___x_4467_);
return v_res_4485_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4489_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4490_ = l_Lean_MessageData_ofFormat(v___x_4489_);
return v___x_4490_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4491_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4493_, lean_object* v___x_4494_, lean_object* v___f_4495_, lean_object* v___x_4496_, lean_object* v_givenNames_4497_, lean_object* v_config_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v___x_4504_; 
lean_inc(v_mvarId_4493_);
v___x_4504_ = l_Lean_MVarId_getType(v_mvarId_4493_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4504_);
switch(lean_obj_tag(v_a_4505_))
{
case 7:
{
lean_object* v_binderName_4506_; lean_object* v_binderType_4507_; lean_object* v_body_4508_; uint8_t v_binderInfo_4509_; lean_object* v___x_4510_; lean_object* v___f_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v_binderName_4506_ = lean_ctor_get(v_a_4505_, 0);
lean_inc(v_binderName_4506_);
v_binderType_4507_ = lean_ctor_get(v_a_4505_, 1);
lean_inc_ref_n(v_binderType_4507_, 2);
v_body_4508_ = lean_ctor_get(v_a_4505_, 2);
lean_inc_ref(v_body_4508_);
v_binderInfo_4509_ = lean_ctor_get_uint8(v_a_4505_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4505_);
v___x_4510_ = lean_box(v_binderInfo_4509_);
v___f_4511_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4511_, 0, v___x_4494_);
lean_closure_set(v___f_4511_, 1, v_binderName_4506_);
lean_closure_set(v___f_4511_, 2, v_body_4508_);
lean_closure_set(v___f_4511_, 3, v___x_4510_);
lean_closure_set(v___f_4511_, 4, v___f_4495_);
lean_closure_set(v___f_4511_, 5, v___x_4496_);
lean_closure_set(v___f_4511_, 6, v_mvarId_4493_);
lean_closure_set(v___f_4511_, 7, v_binderType_4507_);
v___x_4512_ = lean_unsigned_to_nat(1u);
v___x_4513_ = lean_mk_empty_array_with_capacity(v___x_4512_);
v___x_4514_ = lean_array_push(v___x_4513_, v_binderType_4507_);
v___x_4515_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4514_, v_givenNames_4497_, v___f_4511_, v_config_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4515_;
}
case 8:
{
lean_object* v_declName_4516_; lean_object* v_type_4517_; lean_object* v_value_4518_; lean_object* v_body_4519_; uint8_t v_nondep_4520_; lean_object* v___x_4521_; lean_object* v___f_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v_declName_4516_ = lean_ctor_get(v_a_4505_, 0);
lean_inc(v_declName_4516_);
v_type_4517_ = lean_ctor_get(v_a_4505_, 1);
lean_inc_ref_n(v_type_4517_, 2);
v_value_4518_ = lean_ctor_get(v_a_4505_, 2);
lean_inc_ref_n(v_value_4518_, 2);
v_body_4519_ = lean_ctor_get(v_a_4505_, 3);
lean_inc_ref(v_body_4519_);
v_nondep_4520_ = lean_ctor_get_uint8(v_a_4505_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4505_);
v___x_4521_ = lean_box(v_nondep_4520_);
v___f_4522_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4522_, 0, v___x_4494_);
lean_closure_set(v___f_4522_, 1, v_declName_4516_);
lean_closure_set(v___f_4522_, 2, v_body_4519_);
lean_closure_set(v___f_4522_, 3, v___x_4521_);
lean_closure_set(v___f_4522_, 4, v___f_4495_);
lean_closure_set(v___f_4522_, 5, v_value_4518_);
lean_closure_set(v___f_4522_, 6, v___x_4496_);
lean_closure_set(v___f_4522_, 7, v_mvarId_4493_);
lean_closure_set(v___f_4522_, 8, v_type_4517_);
v___x_4523_ = lean_unsigned_to_nat(2u);
v___x_4524_ = lean_mk_empty_array_with_capacity(v___x_4523_);
v___x_4525_ = lean_array_push(v___x_4524_, v_type_4517_);
v___x_4526_ = lean_array_push(v___x_4525_, v_value_4518_);
v___x_4527_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4526_, v_givenNames_4497_, v___f_4522_, v_config_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4527_;
}
default: 
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
lean_dec(v_a_4505_);
lean_dec(v_givenNames_4497_);
lean_dec_ref(v___f_4495_);
lean_dec_ref(v___x_4494_);
v___x_4528_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4529_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4496_, v_mvarId_4493_, v___x_4528_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4529_;
}
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec(v_givenNames_4497_);
lean_dec(v___x_4496_);
lean_dec_ref(v___f_4495_);
lean_dec_ref(v___x_4494_);
lean_dec(v_mvarId_4493_);
v_a_4530_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4504_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4504_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4538_, lean_object* v___x_4539_, lean_object* v___f_4540_, lean_object* v___x_4541_, lean_object* v_givenNames_4542_, lean_object* v_config_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4538_, v___x_4539_, v___f_4540_, v___x_4541_, v_givenNames_4542_, v_config_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec_ref(v_config_4543_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4550_, lean_object* v___x_4551_, lean_object* v_givenNames_4552_, lean_object* v_config_4553_, lean_object* v_mvarId_4554_, lean_object* v_fvars_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___f_4561_; lean_object* v___f_4562_; lean_object* v___x_4563_; 
lean_inc_n(v_mvarId_4554_, 2);
v___f_4561_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4561_, 0, v_mvarId_4554_);
lean_closure_set(v___f_4561_, 1, v_fvars_4555_);
v___f_4562_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4562_, 0, v_mvarId_4554_);
lean_closure_set(v___f_4562_, 1, v___x_4550_);
lean_closure_set(v___f_4562_, 2, v___f_4561_);
lean_closure_set(v___f_4562_, 3, v___x_4551_);
lean_closure_set(v___f_4562_, 4, v_givenNames_4552_);
lean_closure_set(v___f_4562_, 5, v_config_4553_);
v___x_4563_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4554_, v___f_4562_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4564_, lean_object* v___x_4565_, lean_object* v_givenNames_4566_, lean_object* v_config_4567_, lean_object* v_mvarId_4568_, lean_object* v_fvars_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4564_, v___x_4565_, v_givenNames_4566_, v_config_4567_, v_mvarId_4568_, v_fvars_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4576_, lean_object* v_fvarId_4577_, lean_object* v_givenNames_4578_, lean_object* v_config_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4576_);
v___x_4586_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4576_, v___x_4585_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v___x_4587_; lean_object* v___f_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; uint8_t v___x_4592_; lean_object* v___x_4593_; 
lean_dec_ref(v___x_4586_);
v___x_4587_ = l_Lean_instInhabitedExpr;
v___f_4588_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4588_, 0, v___x_4587_);
lean_closure_set(v___f_4588_, 1, v___x_4585_);
lean_closure_set(v___f_4588_, 2, v_givenNames_4578_);
lean_closure_set(v___f_4588_, 3, v_config_4579_);
v___x_4589_ = lean_unsigned_to_nat(1u);
v___x_4590_ = lean_mk_empty_array_with_capacity(v___x_4589_);
v___x_4591_ = lean_array_push(v___x_4590_, v_fvarId_4577_);
v___x_4592_ = 0;
v___x_4593_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4576_, v___x_4591_, v___f_4588_, v___x_4592_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
return v___x_4593_;
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
lean_dec_ref(v_config_4579_);
lean_dec(v_givenNames_4578_);
lean_dec(v_fvarId_4577_);
lean_dec(v_mvarId_4576_);
v_a_4594_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4586_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4586_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4602_, lean_object* v_fvarId_4603_, lean_object* v_givenNames_4604_, lean_object* v_config_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4602_, v_fvarId_4603_, v_givenNames_4604_, v_config_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4612_, lean_object* v___x_4613_, lean_object* v_config_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v___x_4620_; 
lean_inc(v___x_4613_);
lean_inc(v_mvarId_4612_);
v___x_4620_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4612_, v___x_4613_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v___x_4621_; 
lean_dec_ref(v___x_4620_);
lean_inc(v_mvarId_4612_);
v___x_4621_ = l_Lean_MVarId_getType(v_mvarId_4612_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4623_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc_n(v_a_4622_, 2);
lean_dec_ref(v___x_4621_);
v___x_4623_ = l_Lean_Meta_liftLets(v_a_4622_, v_config_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; uint8_t v___x_4625_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_a_4624_);
lean_dec_ref(v___x_4623_);
v___x_4625_ = lean_expr_eqv(v_a_4622_, v_a_4624_);
lean_dec(v_a_4622_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
lean_dec(v___x_4613_);
v___x_4626_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4612_, v_a_4624_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
return v___x_4626_;
}
else
{
lean_object* v___x_4627_; 
lean_inc(v_mvarId_4612_);
v___x_4627_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4613_, v_mvarId_4612_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v___x_4628_; 
lean_dec_ref(v___x_4627_);
v___x_4628_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4612_, v_a_4624_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
return v___x_4628_;
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec(v_a_4624_);
lean_dec(v_mvarId_4612_);
v_a_4629_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4627_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4627_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec(v_a_4622_);
lean_dec(v___x_4613_);
lean_dec(v_mvarId_4612_);
v_a_4637_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4623_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4623_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_dec_ref(v_config_4614_);
lean_dec(v___x_4613_);
lean_dec(v_mvarId_4612_);
v_a_4645_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4621_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4621_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
lean_dec_ref(v_config_4614_);
lean_dec(v___x_4613_);
lean_dec(v_mvarId_4612_);
v_a_4653_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4655_ = v___x_4620_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4620_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4661_, lean_object* v___x_4662_, lean_object* v_config_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4661_, v___x_4662_, v_config_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4673_, lean_object* v_config_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v___x_4680_; lean_object* v___f_4681_; lean_object* v___x_4682_; 
v___x_4680_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4673_);
v___f_4681_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4681_, 0, v_mvarId_4673_);
lean_closure_set(v___f_4681_, 1, v___x_4680_);
lean_closure_set(v___f_4681_, 2, v_config_4674_);
v___x_4682_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4673_, v___f_4681_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4683_, lean_object* v_config_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_Lean_MVarId_liftLets(v_mvarId_4683_, v_config_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4691_, lean_object* v_fvars_4692_, lean_object* v_targetNew_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4691_, v_targetNew_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4713_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4702_ = v___x_4699_;
v_isShared_4703_ = v_isSharedCheck_4713_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4699_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4713_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; size_t v_sz_4705_; size_t v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v___x_4704_ = lean_box(0);
v_sz_4705_ = lean_array_size(v_fvars_4692_);
v___x_4706_ = ((size_t)0ULL);
v___x_4707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4705_, v___x_4706_, v_fvars_4692_);
v___x_4708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4707_);
lean_ctor_set(v___x_4708_, 1, v_a_4700_);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4704_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4709_);
v___x_4711_ = v___x_4702_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_dec_ref(v_fvars_4692_);
v_a_4714_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4699_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4699_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4722_, lean_object* v_fvars_4723_, lean_object* v_targetNew_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4722_, v_fvars_4723_, v_targetNew_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4731_, lean_object* v_config_4732_, lean_object* v___f_4733_, lean_object* v___x_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_){
_start:
{
lean_object* v___x_4740_; 
lean_inc(v_mvarId_4731_);
v___x_4740_ = l_Lean_MVarId_getType(v_mvarId_4731_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4740_);
switch(lean_obj_tag(v_a_4741_))
{
case 7:
{
lean_object* v_binderName_4742_; lean_object* v_binderType_4743_; lean_object* v_body_4744_; uint8_t v_binderInfo_4745_; lean_object* v___x_4746_; 
v_binderName_4742_ = lean_ctor_get(v_a_4741_, 0);
lean_inc(v_binderName_4742_);
v_binderType_4743_ = lean_ctor_get(v_a_4741_, 1);
lean_inc_ref_n(v_binderType_4743_, 2);
v_body_4744_ = lean_ctor_get(v_a_4741_, 2);
lean_inc_ref(v_body_4744_);
v_binderInfo_4745_ = lean_ctor_get_uint8(v_a_4741_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4741_);
v___x_4746_ = l_Lean_Meta_liftLets(v_binderType_4743_, v_config_4732_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; uint8_t v___x_4755_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc(v_a_4747_);
lean_dec_ref(v___x_4746_);
v___x_4755_ = lean_expr_eqv(v_binderType_4743_, v_a_4747_);
lean_dec_ref(v_binderType_4743_);
if (v___x_4755_ == 0)
{
lean_dec(v___x_4734_);
lean_dec(v_mvarId_4731_);
v___y_4749_ = v___y_4735_;
v___y_4750_ = v___y_4736_;
v___y_4751_ = v___y_4737_;
v___y_4752_ = v___y_4738_;
goto v___jp_4748_;
}
else
{
lean_object* v___x_4756_; 
v___x_4756_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4734_, v_mvarId_4731_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_dec_ref(v___x_4756_);
v___y_4749_ = v___y_4735_;
v___y_4750_ = v___y_4736_;
v___y_4751_ = v___y_4737_;
v___y_4752_ = v___y_4738_;
goto v___jp_4748_;
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
lean_dec(v_a_4747_);
lean_dec_ref(v_body_4744_);
lean_dec(v_binderName_4742_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec_ref(v___f_4733_);
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4756_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4756_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
v___jp_4748_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = l_Lean_Expr_forallE___override(v_binderName_4742_, v_a_4747_, v_body_4744_, v_binderInfo_4745_);
v___x_4754_ = lean_apply_6(v___f_4733_, v___x_4753_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, lean_box(0));
return v___x_4754_;
}
}
else
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
lean_dec_ref(v_body_4744_);
lean_dec_ref(v_binderType_4743_);
lean_dec(v_binderName_4742_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___x_4734_);
lean_dec_ref(v___f_4733_);
lean_dec(v_mvarId_4731_);
v_a_4765_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4746_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4746_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
case 8:
{
lean_object* v_declName_4773_; lean_object* v_type_4774_; lean_object* v_value_4775_; lean_object* v_body_4776_; uint8_t v_nondep_4777_; lean_object* v___x_4778_; 
v_declName_4773_ = lean_ctor_get(v_a_4741_, 0);
lean_inc(v_declName_4773_);
v_type_4774_ = lean_ctor_get(v_a_4741_, 1);
lean_inc_ref_n(v_type_4774_, 2);
v_value_4775_ = lean_ctor_get(v_a_4741_, 2);
lean_inc_ref(v_value_4775_);
v_body_4776_ = lean_ctor_get(v_a_4741_, 3);
lean_inc_ref(v_body_4776_);
v_nondep_4777_ = lean_ctor_get_uint8(v_a_4741_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4741_);
lean_inc_ref(v_config_4732_);
v___x_4778_ = l_Lean_Meta_liftLets(v_type_4774_, v_config_4732_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; lean_object* v___x_4780_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref(v___x_4778_);
lean_inc_ref(v_value_4775_);
v___x_4780_ = l_Lean_Meta_liftLets(v_value_4775_, v_config_4732_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v___y_4783_; lean_object* v___y_4784_; lean_object* v___y_4785_; lean_object* v___y_4786_; uint8_t v___y_4790_; uint8_t v___x_4800_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref(v___x_4780_);
v___x_4800_ = lean_expr_eqv(v_type_4774_, v_a_4779_);
lean_dec_ref(v_type_4774_);
if (v___x_4800_ == 0)
{
lean_dec_ref(v_value_4775_);
v___y_4790_ = v___x_4800_;
goto v___jp_4789_;
}
else
{
uint8_t v___x_4801_; 
v___x_4801_ = lean_expr_eqv(v_value_4775_, v_a_4781_);
lean_dec_ref(v_value_4775_);
v___y_4790_ = v___x_4801_;
goto v___jp_4789_;
}
v___jp_4782_:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = l_Lean_Expr_letE___override(v_declName_4773_, v_a_4779_, v_a_4781_, v_body_4776_, v_nondep_4777_);
v___x_4788_ = lean_apply_6(v___f_4733_, v___x_4787_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, lean_box(0));
return v___x_4788_;
}
v___jp_4789_:
{
if (v___y_4790_ == 0)
{
lean_dec(v___x_4734_);
lean_dec(v_mvarId_4731_);
v___y_4783_ = v___y_4735_;
v___y_4784_ = v___y_4736_;
v___y_4785_ = v___y_4737_;
v___y_4786_ = v___y_4738_;
goto v___jp_4782_;
}
else
{
lean_object* v___x_4791_; 
v___x_4791_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4734_, v_mvarId_4731_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_dec_ref(v___x_4791_);
v___y_4783_ = v___y_4735_;
v___y_4784_ = v___y_4736_;
v___y_4785_ = v___y_4737_;
v___y_4786_ = v___y_4738_;
goto v___jp_4782_;
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec(v_a_4781_);
lean_dec(v_a_4779_);
lean_dec_ref(v_body_4776_);
lean_dec(v_declName_4773_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec_ref(v___f_4733_);
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4791_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4791_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
lean_dec(v_a_4779_);
lean_dec_ref(v_body_4776_);
lean_dec_ref(v_value_4775_);
lean_dec_ref(v_type_4774_);
lean_dec(v_declName_4773_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___x_4734_);
lean_dec_ref(v___f_4733_);
lean_dec(v_mvarId_4731_);
v_a_4802_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4780_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4780_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
lean_dec_ref(v_body_4776_);
lean_dec_ref(v_value_4775_);
lean_dec_ref(v_type_4774_);
lean_dec(v_declName_4773_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___x_4734_);
lean_dec_ref(v___f_4733_);
lean_dec_ref(v_config_4732_);
lean_dec(v_mvarId_4731_);
v_a_4810_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4778_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4778_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
default: 
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
lean_dec(v_a_4741_);
lean_dec_ref(v___f_4733_);
lean_dec_ref(v_config_4732_);
v___x_4818_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4819_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4734_, v_mvarId_4731_, v___x_4818_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
return v___x_4819_;
}
}
}
else
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___x_4734_);
lean_dec_ref(v___f_4733_);
lean_dec_ref(v_config_4732_);
lean_dec(v_mvarId_4731_);
v_a_4820_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4740_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4740_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4828_, lean_object* v_config_4829_, lean_object* v___f_4830_, lean_object* v___x_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4828_, v_config_4829_, v___f_4830_, v___x_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4838_, lean_object* v___x_4839_, lean_object* v_mvarId_4840_, lean_object* v_fvars_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v___f_4847_; lean_object* v___f_4848_; lean_object* v___x_4849_; 
lean_inc_n(v_mvarId_4840_, 2);
v___f_4847_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4847_, 0, v_mvarId_4840_);
lean_closure_set(v___f_4847_, 1, v_fvars_4841_);
v___f_4848_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4848_, 0, v_mvarId_4840_);
lean_closure_set(v___f_4848_, 1, v_config_4838_);
lean_closure_set(v___f_4848_, 2, v___f_4847_);
lean_closure_set(v___f_4848_, 3, v___x_4839_);
v___x_4849_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4840_, v___f_4848_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4850_, lean_object* v___x_4851_, lean_object* v_mvarId_4852_, lean_object* v_fvars_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4850_, v___x_4851_, v_mvarId_4852_, v_fvars_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4860_, lean_object* v_fvarId_4861_, lean_object* v_config_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4860_);
v___x_4869_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4860_, v___x_4868_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v___f_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; lean_object* v___x_4875_; 
lean_dec_ref(v___x_4869_);
v___f_4870_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4870_, 0, v_config_4862_);
lean_closure_set(v___f_4870_, 1, v___x_4868_);
v___x_4871_ = lean_unsigned_to_nat(1u);
v___x_4872_ = lean_mk_empty_array_with_capacity(v___x_4871_);
v___x_4873_ = lean_array_push(v___x_4872_, v_fvarId_4861_);
v___x_4874_ = 0;
v___x_4875_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4860_, v___x_4873_, v___f_4870_, v___x_4874_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4884_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4878_ = v___x_4875_;
v_isShared_4879_ = v_isSharedCheck_4884_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4884_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v_snd_4880_; lean_object* v___x_4882_; 
v_snd_4880_ = lean_ctor_get(v_a_4876_, 1);
lean_inc(v_snd_4880_);
lean_dec(v_a_4876_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v_snd_4880_);
v___x_4882_ = v___x_4878_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_snd_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
v_a_4885_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4875_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4875_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec_ref(v_config_4862_);
lean_dec(v_fvarId_4861_);
lean_dec(v_mvarId_4860_);
v_a_4893_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4869_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4869_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4901_, lean_object* v_fvarId_4902_, lean_object* v_config_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4901_, v_fvarId_4902_, v_config_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4910_, lean_object* v___x_4911_, uint8_t v_failIfUnchanged_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v___x_4918_; 
lean_inc(v___x_4911_);
lean_inc(v_mvarId_4910_);
v___x_4918_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4910_, v___x_4911_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v___x_4919_; 
lean_dec_ref(v___x_4918_);
lean_inc(v_mvarId_4910_);
v___x_4919_ = l_Lean_MVarId_getType(v_mvarId_4910_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; lean_object* v___x_4921_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
lean_inc_n(v_a_4920_, 2);
lean_dec_ref(v___x_4919_);
v___x_4921_ = l_Lean_Meta_letToHave(v_a_4920_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4921_) == 0)
{
if (v_failIfUnchanged_4912_ == 0)
{
lean_object* v_a_4922_; lean_object* v___x_4923_; 
lean_dec(v_a_4920_);
lean_dec(v___x_4911_);
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref(v___x_4921_);
v___x_4923_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4910_, v_a_4922_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
return v___x_4923_;
}
else
{
lean_object* v_a_4924_; uint8_t v___x_4925_; 
v_a_4924_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4924_);
lean_dec_ref(v___x_4921_);
v___x_4925_ = lean_expr_eqv(v_a_4920_, v_a_4924_);
lean_dec(v_a_4920_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; 
lean_dec(v___x_4911_);
v___x_4926_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4910_, v_a_4924_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
return v___x_4926_;
}
else
{
lean_object* v___x_4927_; 
lean_inc(v_mvarId_4910_);
v___x_4927_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4911_, v_mvarId_4910_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v___x_4928_; 
lean_dec_ref(v___x_4927_);
v___x_4928_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4910_, v_a_4924_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
return v___x_4928_;
}
else
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
lean_dec(v_a_4924_);
lean_dec(v_mvarId_4910_);
v_a_4929_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4931_ = v___x_4927_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4927_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
lean_dec(v_a_4920_);
lean_dec(v___x_4911_);
lean_dec(v_mvarId_4910_);
v_a_4937_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4921_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4921_);
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
lean_dec(v___x_4911_);
lean_dec(v_mvarId_4910_);
v_a_4945_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___x_4919_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4919_);
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
else
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
lean_dec(v___x_4911_);
lean_dec(v_mvarId_4910_);
v_a_4953_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4918_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4918_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4961_, lean_object* v___x_4962_, lean_object* v_failIfUnchanged_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4969_; lean_object* v_res_4970_; 
v_failIfUnchanged_boxed_4969_ = lean_unbox(v_failIfUnchanged_4963_);
v_res_4970_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4961_, v___x_4962_, v_failIfUnchanged_boxed_4969_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4974_, uint8_t v_failIfUnchanged_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___f_4983_; lean_object* v___x_4984_; 
v___x_4981_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4982_ = lean_box(v_failIfUnchanged_4975_);
lean_inc(v_mvarId_4974_);
v___f_4983_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4983_, 0, v_mvarId_4974_);
lean_closure_set(v___f_4983_, 1, v___x_4981_);
lean_closure_set(v___f_4983_, 2, v___x_4982_);
v___x_4984_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4974_, v___f_4983_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4985_, lean_object* v_failIfUnchanged_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4992_; lean_object* v_res_4993_; 
v_failIfUnchanged_boxed_4992_ = lean_unbox(v_failIfUnchanged_4986_);
v_res_4993_ = l_Lean_MVarId_letToHave(v_mvarId_4985_, v_failIfUnchanged_boxed_4992_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_);
lean_dec(v_a_4990_);
lean_dec_ref(v_a_4989_);
lean_dec(v_a_4988_);
lean_dec_ref(v_a_4987_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4994_, lean_object* v___x_4995_, lean_object* v_fvarId_4996_, uint8_t v_failIfUnchanged_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v___x_5003_; 
lean_inc(v___x_4995_);
lean_inc(v_mvarId_4994_);
v___x_5003_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4994_, v___x_4995_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v___x_5004_; 
lean_dec_ref(v___x_5003_);
lean_inc(v_fvarId_4996_);
v___x_5004_ = l_Lean_FVarId_getType___redArg(v_fvarId_4996_, v___y_4998_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5004_) == 0)
{
lean_object* v_a_5005_; lean_object* v___x_5006_; 
v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc_n(v_a_5005_, 2);
lean_dec_ref(v___x_5004_);
v___x_5006_ = l_Lean_Meta_letToHave(v_a_5005_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5006_) == 0)
{
if (v_failIfUnchanged_4997_ == 0)
{
lean_object* v_a_5007_; lean_object* v___x_5008_; 
lean_dec(v_a_5005_);
lean_dec(v___x_4995_);
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5007_);
lean_dec_ref(v___x_5006_);
v___x_5008_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4994_, v_fvarId_4996_, v_a_5007_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
return v___x_5008_;
}
else
{
lean_object* v_a_5009_; uint8_t v___x_5010_; 
v_a_5009_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5009_);
lean_dec_ref(v___x_5006_);
v___x_5010_ = lean_expr_eqv(v_a_5005_, v_a_5009_);
lean_dec(v_a_5005_);
if (v___x_5010_ == 0)
{
lean_object* v___x_5011_; 
lean_dec(v___x_4995_);
v___x_5011_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4994_, v_fvarId_4996_, v_a_5009_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
return v___x_5011_;
}
else
{
lean_object* v___x_5012_; 
lean_inc(v_mvarId_4994_);
v___x_5012_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4995_, v_mvarId_4994_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v___x_5013_; 
lean_dec_ref(v___x_5012_);
v___x_5013_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4994_, v_fvarId_4996_, v_a_5009_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
return v___x_5013_;
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_dec(v_a_5009_);
lean_dec(v_fvarId_4996_);
lean_dec(v_mvarId_4994_);
v_a_5014_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_5012_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5012_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
lean_dec(v_a_5005_);
lean_dec(v_fvarId_4996_);
lean_dec(v___x_4995_);
lean_dec(v_mvarId_4994_);
v_a_5022_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5006_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5006_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
lean_dec(v_fvarId_4996_);
lean_dec(v___x_4995_);
lean_dec(v_mvarId_4994_);
v_a_5030_ = lean_ctor_get(v___x_5004_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___x_5004_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_5004_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
lean_dec(v_fvarId_4996_);
lean_dec(v___x_4995_);
lean_dec(v_mvarId_4994_);
v_a_5038_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5040_ = v___x_5003_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5003_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5046_, lean_object* v___x_5047_, lean_object* v_fvarId_5048_, lean_object* v_failIfUnchanged_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5055_; lean_object* v_res_5056_; 
v_failIfUnchanged_boxed_5055_ = lean_unbox(v_failIfUnchanged_5049_);
v_res_5056_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5046_, v___x_5047_, v_fvarId_5048_, v_failIfUnchanged_boxed_5055_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5057_, lean_object* v_fvarId_5058_, uint8_t v_failIfUnchanged_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___f_5067_; lean_object* v___x_5068_; 
v___x_5065_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5066_ = lean_box(v_failIfUnchanged_5059_);
lean_inc(v_mvarId_5057_);
v___f_5067_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5067_, 0, v_mvarId_5057_);
lean_closure_set(v___f_5067_, 1, v___x_5065_);
lean_closure_set(v___f_5067_, 2, v_fvarId_5058_);
lean_closure_set(v___f_5067_, 3, v___x_5066_);
v___x_5068_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5057_, v___f_5067_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5069_, lean_object* v_fvarId_5070_, lean_object* v_failIfUnchanged_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5077_; lean_object* v_res_5078_; 
v_failIfUnchanged_boxed_5077_ = lean_unbox(v_failIfUnchanged_5071_);
v_res_5078_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5069_, v_fvarId_5070_, v_failIfUnchanged_boxed_5077_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
return v_res_5078_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LetToHave(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
