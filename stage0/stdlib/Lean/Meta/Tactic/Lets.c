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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_ExtractLets_flushDecls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_flushDecls___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Meta_ExtractLets_flushDecls___closed__1(void){
_start:
{
lean_object* v_toSave_655_; lean_object* v___x_656_; 
v_toSave_655_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_toSave_655_);
lean_ctor_set(v___x_656_, 1, v_toSave_655_);
return v___x_656_;
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
v___x_670_ = lean_obj_once(&l_Lean_Meta_ExtractLets_flushDecls___closed__1, &l_Lean_Meta_ExtractLets_flushDecls___closed__1_once, _init_l_Lean_Meta_ExtractLets_flushDecls___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_k_786_, lean_object* v_decls_787_, lean_object* v_lctx_788_){
_start:
{
lean_object* v___y_790_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_array_get_size(v_decls_787_);
v___x_799_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_800_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_801_ = lean_nat_dec_lt(v___x_797_, v___x_798_);
if (v___x_801_ == 0)
{
lean_dec_ref(v_lctx_788_);
lean_dec_ref(v_decls_787_);
v___y_790_ = v___x_799_;
goto v___jp_789_;
}
else
{
lean_object* v___f_802_; uint8_t v___x_803_; 
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1), 3, 1);
lean_closure_set(v___f_802_, 0, v_lctx_788_);
v___x_803_ = lean_nat_dec_le(v___x_798_, v___x_798_);
if (v___x_803_ == 0)
{
if (v___x_801_ == 0)
{
lean_dec_ref(v___f_802_);
lean_dec_ref(v_decls_787_);
v___y_790_ = v___x_799_;
goto v___jp_789_;
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)0ULL);
v___x_805_ = lean_usize_of_nat(v___x_798_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_800_, v___f_802_, v_decls_787_, v___x_804_, v___x_805_, v___x_799_);
v___y_790_ = v___x_806_;
goto v___jp_789_;
}
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_798_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_800_, v___f_802_, v_decls_787_, v___x_807_, v___x_808_, v___x_799_);
v___y_790_ = v___x_809_;
goto v___jp_789_;
}
}
v___jp_789_:
{
lean_object* v___x_791_; size_t v_sz_792_; size_t v___x_793_; lean_object* v_decls_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_791_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_792_ = lean_array_size(v___y_790_);
v___x_793_ = ((size_t)0ULL);
v_decls_794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_791_, v___f_783_, v_sz_792_, v___x_793_, v___y_790_);
v___x_795_ = lean_array_to_list(v_decls_794_);
v___x_796_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_784_, v_inst_785_, v___x_795_, v_k_786_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_decls_814_, lean_object* v_k_815_){
_start:
{
lean_object* v_toBind_816_; lean_object* v___f_817_; lean_object* v___f_818_; lean_object* v___x_819_; 
v_toBind_816_ = lean_ctor_get(v_inst_811_, 1);
lean_inc(v_toBind_816_);
v___f_817_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_818_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_818_, 0, v___f_817_);
lean_closure_set(v___f_818_, 1, v_inst_812_);
lean_closure_set(v___f_818_, 2, v_inst_811_);
lean_closure_set(v___f_818_, 3, v_k_815_);
lean_closure_set(v___f_818_, 4, v_decls_814_);
v___x_819_ = lean_apply_4(v_toBind_816_, lean_box(0), lean_box(0), v_inst_813_, v___f_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_820_, lean_object* v_00_u03b1_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_decls_825_, lean_object* v_k_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_822_, v_inst_823_, v_inst_824_, v_decls_825_, v_k_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_828_, size_t v_i_829_, size_t v_stop_830_, lean_object* v_b_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_eq(v_i_829_, v_stop_830_);
if (v___x_832_ == 0)
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; lean_object* v_decl_836_; uint8_t v_isLet_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_sub(v_i_829_, v___x_833_);
v___x_835_ = lean_array_uget_borrowed(v_as_828_, v___x_834_);
v_decl_836_ = lean_ctor_get(v___x_835_, 0);
v_isLet_837_ = lean_ctor_get_uint8(v___x_835_, sizeof(void*)*1);
v___x_838_ = l_Lean_LocalDecl_userName(v_decl_836_);
v___x_839_ = l_Lean_LocalDecl_type(v_decl_836_);
v___x_840_ = l_Lean_LocalDecl_value(v_decl_836_, v___x_832_);
lean_inc_ref(v_decl_836_);
v___x_841_ = l_Lean_LocalDecl_toExpr(v_decl_836_);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_mk_empty_array_with_capacity(v___x_842_);
v___x_844_ = lean_array_push(v___x_843_, v___x_841_);
v___x_845_ = lean_expr_abstract(v_b_831_, v___x_844_);
lean_dec_ref(v___x_844_);
lean_dec_ref(v_b_831_);
if (v_isLet_837_ == 0)
{
uint8_t v___x_846_; lean_object* v___x_847_; 
v___x_846_ = 1;
v___x_847_ = l_Lean_Expr_letE___override(v___x_838_, v___x_839_, v___x_840_, v___x_845_, v___x_846_);
v_i_829_ = v___x_834_;
v_b_831_ = v___x_847_;
goto _start;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Expr_letE___override(v___x_838_, v___x_839_, v___x_840_, v___x_845_, v___x_832_);
v_i_829_ = v___x_834_;
v_b_831_ = v___x_849_;
goto _start;
}
}
else
{
return v_b_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object* v_as_851_, lean_object* v_i_852_, lean_object* v_stop_853_, lean_object* v_b_854_){
_start:
{
size_t v_i_boxed_855_; size_t v_stop_boxed_856_; lean_object* v_res_857_; 
v_i_boxed_855_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_stop_boxed_856_ = lean_unbox_usize(v_stop_853_);
lean_dec(v_stop_853_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_851_, v_i_boxed_855_, v_stop_boxed_856_, v_b_854_);
lean_dec_ref(v_as_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object* v_decls_858_, lean_object* v_e_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_860_ = lean_array_get_size(v_decls_858_);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_nat_dec_lt(v___x_861_, v___x_860_);
if (v___x_862_ == 0)
{
return v_e_859_;
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_usize_of_nat(v___x_860_);
v___x_864_ = ((size_t)0ULL);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_858_, v___x_863_, v___x_864_, v_e_859_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object* v_decls_866_, lean_object* v_e_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_866_, v_e_867_);
lean_dec_ref(v_decls_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object* v_fvarId_869_, size_t v_sz_870_, size_t v_i_871_, lean_object* v_bs_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_873_ == 0)
{
return v_bs_872_;
}
else
{
lean_object* v_v_874_; lean_object* v_decl_875_; lean_object* v___x_876_; lean_object* v_bs_x27_877_; lean_object* v___y_879_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_v_874_ = lean_array_uget(v_bs_872_, v_i_871_);
v_decl_875_ = lean_ctor_get(v_v_874_, 0);
v___x_876_ = lean_unsigned_to_nat(0u);
v_bs_x27_877_ = lean_array_uset(v_bs_872_, v_i_871_, v___x_876_);
v___x_884_ = l_Lean_LocalDecl_fvarId(v_decl_875_);
v___x_885_ = l_Lean_instBEqFVarId_beq(v___x_884_, v_fvarId_869_);
lean_dec(v___x_884_);
if (v___x_885_ == 0)
{
v___y_879_ = v_v_874_;
goto v___jp_878_;
}
else
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_inc_ref(v_decl_875_);
v_isSharedCheck_892_ = !lean_is_exclusive(v_v_874_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_v_874_, 0);
lean_dec(v_unused_893_);
v___x_887_ = v_v_874_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_v_874_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_decl_875_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*1, v___x_885_);
v___y_879_ = v___x_890_;
goto v___jp_878_;
}
}
}
v___jp_878_:
{
size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_871_, v___x_880_);
v___x_882_ = lean_array_uset(v_bs_x27_877_, v_i_871_, v___y_879_);
v_i_871_ = v___x_881_;
v_bs_872_ = v___x_882_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object* v_fvarId_894_, lean_object* v_sz_895_, lean_object* v_i_896_, lean_object* v_bs_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_i_boxed_899_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_894_, v_sz_boxed_898_, v_i_boxed_899_, v_bs_897_);
lean_dec(v_fvarId_894_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object* v_fvarId_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; lean_object* v_givenNames_905_; lean_object* v_decls_906_; lean_object* v_valueMap_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_920_; 
v___x_904_ = lean_st_ref_take(v_a_902_);
v_givenNames_905_ = lean_ctor_get(v___x_904_, 0);
v_decls_906_ = lean_ctor_get(v___x_904_, 1);
v_valueMap_907_ = lean_ctor_get(v___x_904_, 2);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_920_ == 0)
{
v___x_909_ = v___x_904_;
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_valueMap_907_);
lean_inc(v_decls_906_);
lean_inc(v_givenNames_905_);
lean_dec(v___x_904_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
size_t v_sz_911_; size_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v_sz_911_ = lean_array_size(v_decls_906_);
v___x_912_ = ((size_t)0ULL);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_901_, v_sz_911_, v___x_912_, v_decls_906_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_913_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_givenNames_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_valueMap_907_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_st_ref_set(v_a_902_, v___x_915_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object* v_fvarId_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec(v_fvarId_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object* v_fvarId_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_925_, v_a_928_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object* v_fvarId_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_fvarId_935_);
return v_res_944_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0(lean_object* v_fvarId_945_, lean_object* v_x_946_){
_start:
{
lean_object* v_decl_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_decl_947_ = lean_ctor_get(v_x_946_, 0);
v___x_948_ = l_Lean_LocalDecl_fvarId(v_decl_947_);
v___x_949_ = l_Lean_instBEqFVarId_beq(v___x_948_, v_fvarId_945_);
lean_dec(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0___boxed(lean_object* v_fvarId_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0(v_fvarId_950_, v_x_951_);
lean_dec_ref(v_x_951_);
lean_dec(v_fvarId_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(lean_object* v___x_954_, lean_object* v_as_955_, size_t v_i_956_, size_t v_stop_957_, lean_object* v_b_958_){
_start:
{
lean_object* v___y_960_; uint8_t v___x_964_; 
v___x_964_ = lean_usize_dec_eq(v_i_956_, v_stop_957_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v_decl_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_965_ = lean_array_uget_borrowed(v_as_955_, v_i_956_);
v_decl_966_ = lean_ctor_get(v___x_965_, 0);
v___x_967_ = l_Lean_LocalDecl_fvarId(v_decl_966_);
lean_inc_ref(v___x_954_);
v___x_968_ = l_Lean_LocalContext_contains(v___x_954_, v___x_967_);
lean_dec(v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
lean_inc(v___x_965_);
v___x_969_ = lean_array_push(v_b_958_, v___x_965_);
v___y_960_ = v___x_969_;
goto v___jp_959_;
}
else
{
v___y_960_ = v_b_958_;
goto v___jp_959_;
}
}
else
{
lean_dec_ref(v___x_954_);
return v_b_958_;
}
v___jp_959_:
{
size_t v___x_961_; size_t v___x_962_; 
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_i_956_, v___x_961_);
v_i_956_ = v___x_962_;
v_b_958_ = v___y_960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2___boxed(lean_object* v___x_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_stop_973_, lean_object* v_b_974_){
_start:
{
size_t v_i_boxed_975_; size_t v_stop_boxed_976_; lean_object* v_res_977_; 
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_stop_boxed_976_ = lean_unbox_usize(v_stop_973_);
lean_dec(v_stop_973_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v___x_970_, v_as_971_, v_i_boxed_975_, v_stop_boxed_976_, v_b_974_);
lean_dec_ref(v_as_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
lean_inc(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
v___x_987_ = lean_apply_8(v_x_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_x_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(v_x_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(lean_object* v_decls_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_1009_; 
lean_inc(v___y_1002_);
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1008_, 0, v_x_999_);
lean_closure_set(v___f_1008_, 1, v___y_1000_);
lean_closure_set(v___f_1008_, 2, v___y_1001_);
lean_closure_set(v___f_1008_, 3, v___y_1002_);
v___x_1009_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_998_, v___f_1008_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1009_) == 0)
{
return v___x_1009_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___boxed(lean_object* v_decls_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v_decls_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(size_t v_sz_1029_, size_t v_i_1030_, lean_object* v_bs_1031_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_lt(v_i_1030_, v_sz_1029_);
if (v___x_1032_ == 0)
{
return v_bs_1031_;
}
else
{
lean_object* v_v_1033_; lean_object* v_decl_1034_; lean_object* v___x_1035_; lean_object* v_bs_x27_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v_v_1033_ = lean_array_uget_borrowed(v_bs_1031_, v_i_1030_);
v_decl_1034_ = lean_ctor_get(v_v_1033_, 0);
lean_inc_ref(v_decl_1034_);
v___x_1035_ = lean_unsigned_to_nat(0u);
v_bs_x27_1036_ = lean_array_uset(v_bs_1031_, v_i_1030_, v___x_1035_);
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_i_1030_, v___x_1037_);
v___x_1039_ = lean_array_uset(v_bs_x27_1036_, v_i_1030_, v_decl_1034_);
v_i_1030_ = v___x_1038_;
v_bs_1031_ = v___x_1039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0___boxed(lean_object* v_sz_1041_, lean_object* v_i_1042_, lean_object* v_bs_1043_){
_start:
{
size_t v_sz_boxed_1044_; size_t v_i_boxed_1045_; lean_object* v_res_1046_; 
v_sz_boxed_1044_ = lean_unbox_usize(v_sz_1041_);
lean_dec(v_sz_1041_);
v_i_boxed_1045_ = lean_unbox_usize(v_i_1042_);
lean_dec(v_i_1042_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_boxed_1044_, v_i_boxed_1045_, v_bs_1043_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(lean_object* v_decls_1047_, lean_object* v_k_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___y_1058_; lean_object* v_lctx_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_lctx_1064_ = lean_ctor_get(v___y_1052_, 2);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_array_get_size(v_decls_1047_);
v___x_1067_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_1068_ = lean_nat_dec_lt(v___x_1065_, v___x_1066_);
if (v___x_1068_ == 0)
{
v___y_1058_ = v___x_1067_;
goto v___jp_1057_;
}
else
{
uint8_t v___x_1069_; 
v___x_1069_ = lean_nat_dec_le(v___x_1066_, v___x_1066_);
if (v___x_1069_ == 0)
{
if (v___x_1068_ == 0)
{
v___y_1058_ = v___x_1067_;
goto v___jp_1057_;
}
else
{
size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = lean_usize_of_nat(v___x_1066_);
lean_inc_ref(v_lctx_1064_);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v_lctx_1064_, v_decls_1047_, v___x_1070_, v___x_1071_, v___x_1067_);
v___y_1058_ = v___x_1072_;
goto v___jp_1057_;
}
}
else
{
size_t v___x_1073_; size_t v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = ((size_t)0ULL);
v___x_1074_ = lean_usize_of_nat(v___x_1066_);
lean_inc_ref(v_lctx_1064_);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v_lctx_1064_, v_decls_1047_, v___x_1073_, v___x_1074_, v___x_1067_);
v___y_1058_ = v___x_1075_;
goto v___jp_1057_;
}
}
v___jp_1057_:
{
size_t v_sz_1059_; size_t v___x_1060_; lean_object* v_decls_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_sz_1059_ = lean_array_size(v___y_1058_);
v___x_1060_ = ((size_t)0ULL);
v_decls_1061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_1059_, v___x_1060_, v___y_1058_);
v___x_1062_ = lean_array_to_list(v_decls_1061_);
v___x_1063_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v___x_1062_, v_k_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec_ref(v___y_1052_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg___boxed(lean_object* v_decls_1076_, lean_object* v_k_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1076_, v_k_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v_decls_1076_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1087_, lean_object* v_k_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v_lctx_1098_; uint8_t v___x_1099_; 
v___x_1097_ = lean_st_ref_get(v_a_1091_);
v_lctx_1098_ = lean_ctor_get(v_a_1092_, 2);
lean_inc_ref(v_lctx_1098_);
v___x_1099_ = l_Lean_LocalContext_contains(v_lctx_1098_, v_fvarId_1087_);
if (v___x_1099_ == 0)
{
lean_object* v_decls_1100_; lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_decls_1100_ = lean_ctor_get(v___x_1097_, 1);
lean_inc_ref(v_decls_1100_);
lean_dec(v___x_1097_);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1101_, 0, v_fvarId_1087_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = l_Array_findIdx_x3f_loop___redArg(v___f_1101_, v_decls_1100_, v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 1)
{
lean_object* v_val_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_val_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1104_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_add(v_val_1104_, v___x_1105_);
lean_dec(v_val_1104_);
v___x_1107_ = l_Array_toSubarray___redArg(v_decls_1100_, v___x_1102_, v___x_1106_);
v___x_1108_ = l_Subarray_copy___redArg(v___x_1107_);
v___x_1109_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v___x_1108_, v_k_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec_ref(v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; 
lean_dec(v___x_1103_);
lean_dec_ref(v_decls_1100_);
lean_inc(v_a_1095_);
lean_inc_ref(v_a_1094_);
lean_inc(v_a_1093_);
lean_inc(v_a_1091_);
lean_inc(v_a_1090_);
lean_inc_ref(v_a_1089_);
v___x_1110_ = lean_apply_8(v_k_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, lean_box(0));
return v___x_1110_;
}
}
else
{
lean_object* v___x_1111_; 
lean_dec(v___x_1097_);
lean_dec(v_fvarId_1087_);
lean_inc(v_a_1095_);
lean_inc_ref(v_a_1094_);
lean_inc(v_a_1093_);
lean_inc(v_a_1091_);
lean_inc(v_a_1090_);
lean_inc_ref(v_a_1089_);
v___x_1111_ = lean_apply_8(v_k_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, lean_box(0));
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1112_, lean_object* v_k_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1112_, v_k_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1123_, lean_object* v_fvarId_1124_, lean_object* v_k_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; 
lean_inc_ref(v_a_1129_);
v___x_1134_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1124_, v_k_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_fvarId_1136_, lean_object* v_k_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1135_, v_fvarId_1136_, v_k_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1(lean_object* v_00_u03b1_1147_, lean_object* v_decls_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v_decls_1148_, v_x_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_decls_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1(v_00_u03b1_1159_, v_decls_1160_, v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_00_u03b1_1171_, lean_object* v_decls_1172_, lean_object* v_k_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
lean_inc_ref(v___y_1177_);
v___x_1182_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1172_, v_k_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_decls_1184_, lean_object* v_k_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_00_u03b1_1183_, v_decls_1184_, v_k_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_decls_1184_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1195_, lean_object* v___y_1196_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_Expr_hasMVar(v_e_1195_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_e_1195_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v_mctx_1201_; lean_object* v___x_1202_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1205_; lean_object* v_cache_1206_; lean_object* v_zetaDeltaFVarIds_1207_; lean_object* v_postponed_1208_; lean_object* v_diag_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1218_; 
v___x_1200_ = lean_st_ref_get(v___y_1196_);
v_mctx_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_mctx_1201_);
lean_dec(v___x_1200_);
v___x_1202_ = l_Lean_instantiateMVarsCore(v_mctx_1201_, v_e_1195_);
v_fst_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_fst_1203_);
v_snd_1204_ = lean_ctor_get(v___x_1202_, 1);
lean_inc(v_snd_1204_);
lean_dec_ref(v___x_1202_);
v___x_1205_ = lean_st_ref_take(v___y_1196_);
v_cache_1206_ = lean_ctor_get(v___x_1205_, 1);
v_zetaDeltaFVarIds_1207_ = lean_ctor_get(v___x_1205_, 2);
v_postponed_1208_ = lean_ctor_get(v___x_1205_, 3);
v_diag_1209_ = lean_ctor_get(v___x_1205_, 4);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v___x_1205_, 0);
lean_dec(v_unused_1219_);
v___x_1211_ = v___x_1205_;
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_diag_1209_);
lean_inc(v_postponed_1208_);
lean_inc(v_zetaDeltaFVarIds_1207_);
lean_inc(v_cache_1206_);
lean_dec(v___x_1205_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_snd_1204_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_snd_1204_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_cache_1206_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_zetaDeltaFVarIds_1207_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_postponed_1208_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_diag_1209_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_st_ref_set(v___y_1196_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_fst_1203_);
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1220_, v___y_1221_);
lean_dec(v___y_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1224_, v___y_1229_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1244_, size_t v_i_1245_, size_t v_stop_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_a_1257_; uint8_t v___x_1263_; 
v___x_1263_ = lean_usize_dec_eq(v_i_1245_, v_stop_1246_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_array_uget_borrowed(v_as_1244_, v_i_1245_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_box(0);
v_a_1257_ = v___x_1265_;
goto v___jp_1256_;
}
else
{
lean_object* v_val_1266_; uint8_t v___y_1268_; uint8_t v___x_1295_; 
v_val_1266_ = lean_ctor_get(v___x_1264_, 0);
v___x_1295_ = l_Lean_LocalDecl_isLet(v_val_1266_, v___x_1263_);
if (v___x_1295_ == 0)
{
v___y_1268_ = v___x_1295_;
goto v___jp_1267_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1266_);
if (v___x_1296_ == 0)
{
v___y_1268_ = v___x_1295_;
goto v___jp_1267_;
}
else
{
goto v___jp_1261_;
}
}
v___jp_1267_:
{
if (v___y_1268_ == 0)
{
goto v___jp_1261_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Lean_LocalDecl_value(v_val_1266_, v___x_1263_);
v___x_1270_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1269_, v___y_1252_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v_givenNames_1273_; lean_object* v_decls_1274_; lean_object* v_valueMap_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1286_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = lean_st_ref_take(v___y_1250_);
v_givenNames_1273_ = lean_ctor_get(v___x_1272_, 0);
v_decls_1274_ = lean_ctor_get(v___x_1272_, 1);
v_valueMap_1275_ = lean_ctor_get(v___x_1272_, 2);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1277_ = v___x_1272_;
v_isShared_1278_ = v_isSharedCheck_1286_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_valueMap_1275_);
lean_inc(v_decls_1274_);
lean_inc(v_givenNames_1273_);
lean_dec(v___x_1272_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1286_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = l_Lean_LocalDecl_fvarId(v_val_1266_);
v___x_1280_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1275_, v_a_1271_, v___x_1279_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 2, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_givenNames_1273_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_decls_1274_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_st_ref_set(v___y_1250_, v___x_1282_);
v___x_1284_ = lean_box(0);
v_a_1257_ = v___x_1284_;
goto v___jp_1256_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1270_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1270_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_b_1247_);
return v___x_1297_;
}
v___jp_1256_:
{
size_t v___x_1258_; size_t v___x_1259_; 
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_add(v_i_1245_, v___x_1258_);
v_i_1245_ = v___x_1259_;
v_b_1247_ = v_a_1257_;
goto _start;
}
v___jp_1261_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_box(0);
v_a_1257_ = v___x_1262_;
goto v___jp_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1298_, lean_object* v_i_1299_, lean_object* v_stop_1300_, lean_object* v_b_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_i_boxed_1310_; size_t v_stop_boxed_1311_; lean_object* v_res_1312_; 
v_i_boxed_1310_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_stop_boxed_1311_ = lean_unbox_usize(v_stop_1300_);
lean_dec(v_stop_1300_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1298_, v_i_boxed_1310_, v_stop_boxed_1311_, v_b_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v_as_1298_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1313_, size_t v_i_1314_, size_t v_stop_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_a_1326_; uint8_t v___x_1332_; 
v___x_1332_ = lean_usize_dec_eq(v_i_1314_, v_stop_1315_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_array_uget_borrowed(v_as_1313_, v_i_1314_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_box(0);
v_a_1326_ = v___x_1334_;
goto v___jp_1325_;
}
else
{
lean_object* v_val_1335_; uint8_t v___y_1337_; uint8_t v___x_1364_; 
v_val_1335_ = lean_ctor_get(v___x_1333_, 0);
v___x_1364_ = l_Lean_LocalDecl_isLet(v_val_1335_, v___x_1332_);
if (v___x_1364_ == 0)
{
v___y_1337_ = v___x_1364_;
goto v___jp_1336_;
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1335_);
if (v___x_1365_ == 0)
{
v___y_1337_ = v___x_1364_;
goto v___jp_1336_;
}
else
{
goto v___jp_1330_;
}
}
v___jp_1336_:
{
if (v___y_1337_ == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = l_Lean_LocalDecl_value(v_val_1335_, v___x_1332_);
v___x_1339_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1338_, v___y_1321_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v_givenNames_1342_; lean_object* v_decls_1343_; lean_object* v_valueMap_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1355_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_st_ref_take(v___y_1319_);
v_givenNames_1342_ = lean_ctor_get(v___x_1341_, 0);
v_decls_1343_ = lean_ctor_get(v___x_1341_, 1);
v_valueMap_1344_ = lean_ctor_get(v___x_1341_, 2);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1346_ = v___x_1341_;
v_isShared_1347_ = v_isSharedCheck_1355_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_valueMap_1344_);
lean_inc(v_decls_1343_);
lean_inc(v_givenNames_1342_);
lean_dec(v___x_1341_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1355_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = l_Lean_LocalDecl_fvarId(v_val_1335_);
v___x_1349_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1344_, v_a_1340_, v___x_1348_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 2, v___x_1349_);
v___x_1351_ = v___x_1346_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_givenNames_1342_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_decls_1343_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_st_ref_set(v___y_1319_, v___x_1351_);
v___x_1353_ = lean_box(0);
v_a_1326_ = v___x_1353_;
goto v___jp_1325_;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1339_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1339_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_b_1316_);
return v___x_1366_;
}
v___jp_1325_:
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_add(v_i_1314_, v___x_1327_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1313_, v___x_1328_, v_stop_1315_, v_a_1326_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1329_;
}
v___jp_1330_:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_box(0);
v_a_1326_ = v___x_1331_;
goto v___jp_1325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1367_, lean_object* v_i_1368_, lean_object* v_stop_1369_, lean_object* v_b_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
size_t v_i_boxed_1379_; size_t v_stop_boxed_1380_; lean_object* v_res_1381_; 
v_i_boxed_1379_ = lean_unbox_usize(v_i_1368_);
lean_dec(v_i_1368_);
v_stop_boxed_1380_ = lean_unbox_usize(v_stop_1369_);
lean_dec(v_stop_1369_);
v_res_1381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1367_, v_i_boxed_1379_, v_stop_boxed_1380_, v_b_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec_ref(v_as_1367_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
lean_object* v_cs_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1412_; 
v_cs_1391_ = lean_ctor_get(v_x_1382_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1393_ = v_x_1382_;
v_isShared_1394_ = v_isSharedCheck_1412_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_cs_1391_);
lean_dec(v_x_1382_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1412_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_array_get_size(v_cs_1391_);
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_nat_dec_lt(v___x_1395_, v___x_1396_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v_cs_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1397_);
v___x_1400_ = v___x_1393_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1397_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_le(v___x_1396_, v___x_1396_);
if (v___x_1402_ == 0)
{
if (v___x_1398_ == 0)
{
lean_object* v___x_1404_; 
lean_dec_ref(v_cs_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1397_);
v___x_1404_ = v___x_1393_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1397_);
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
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
lean_del_object(v___x_1393_);
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = lean_usize_of_nat(v___x_1396_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1391_, v___x_1406_, v___x_1407_, v___x_1397_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_cs_1391_);
return v___x_1408_;
}
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
lean_del_object(v___x_1393_);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1396_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1391_, v___x_1409_, v___x_1410_, v___x_1397_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_cs_1391_);
return v___x_1411_;
}
}
}
}
else
{
lean_object* v_vs_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1434_; 
v_vs_1413_ = lean_ctor_get(v_x_1382_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1415_ = v_x_1382_;
v_isShared_1416_ = v_isSharedCheck_1434_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_vs_1413_);
lean_dec(v_x_1382_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1434_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_array_get_size(v_vs_1413_);
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1422_; 
lean_dec_ref(v_vs_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1419_);
v___x_1422_ = v___x_1415_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1419_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_le(v___x_1418_, v___x_1418_);
if (v___x_1424_ == 0)
{
if (v___x_1420_ == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v_vs_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1419_);
v___x_1426_ = v___x_1415_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1419_);
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
size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
lean_del_object(v___x_1415_);
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = lean_usize_of_nat(v___x_1418_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1413_, v___x_1428_, v___x_1429_, v___x_1419_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_vs_1413_);
return v___x_1430_;
}
}
else
{
size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
lean_del_object(v___x_1415_);
v___x_1431_ = ((size_t)0ULL);
v___x_1432_ = lean_usize_of_nat(v___x_1418_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1413_, v___x_1431_, v___x_1432_, v___x_1419_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_vs_1413_);
return v___x_1433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1435_, size_t v_i_1436_, size_t v_stop_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_eq(v_i_1436_, v_stop_1437_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_array_uget_borrowed(v_as_1435_, v_i_1436_);
lean_inc(v___x_1448_);
v___x_1449_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1448_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; size_t v___x_1451_; size_t v___x_1452_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = ((size_t)1ULL);
v___x_1452_ = lean_usize_add(v_i_1436_, v___x_1451_);
v_i_1436_ = v___x_1452_;
v_b_1438_ = v_a_1450_;
goto _start;
}
else
{
return v___x_1449_;
}
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1438_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1455_, lean_object* v_i_1456_, lean_object* v_stop_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
size_t v_i_boxed_1467_; size_t v_stop_boxed_1468_; lean_object* v_res_1469_; 
v_i_boxed_1467_ = lean_unbox_usize(v_i_1456_);
lean_dec(v_i_1456_);
v_stop_boxed_1468_ = lean_unbox_usize(v_stop_1457_);
lean_dec(v_stop_1457_);
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1455_, v_i_boxed_1467_, v_stop_boxed_1468_, v_b_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v_as_1455_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_root_1489_; lean_object* v_tail_1490_; lean_object* v___x_1491_; 
v_root_1489_ = lean_ctor_get(v_t_1480_, 0);
lean_inc_ref(v_root_1489_);
v_tail_1490_ = lean_ctor_get(v_t_1480_, 1);
lean_inc_ref(v_tail_1490_);
lean_dec_ref(v_t_1480_);
v___x_1491_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1489_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1512_; 
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v___x_1491_, 0);
lean_dec(v_unused_1513_);
v___x_1493_ = v___x_1491_;
v_isShared_1494_ = v_isSharedCheck_1512_;
goto v_resetjp_1492_;
}
else
{
lean_dec(v___x_1491_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1512_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_array_get_size(v_tail_1490_);
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_nat_dec_lt(v___x_1495_, v___x_1496_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1500_; 
lean_dec_ref(v_tail_1490_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1497_);
v___x_1500_ = v___x_1493_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1497_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_nat_dec_le(v___x_1496_, v___x_1496_);
if (v___x_1502_ == 0)
{
if (v___x_1498_ == 0)
{
lean_object* v___x_1504_; 
lean_dec_ref(v_tail_1490_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1497_);
v___x_1504_ = v___x_1493_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1497_);
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
size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
lean_del_object(v___x_1493_);
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = lean_usize_of_nat(v___x_1496_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1490_, v___x_1506_, v___x_1507_, v___x_1497_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_tail_1490_);
return v___x_1508_;
}
}
else
{
size_t v___x_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
lean_del_object(v___x_1493_);
v___x_1509_ = ((size_t)0ULL);
v___x_1510_ = lean_usize_of_nat(v___x_1496_);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1490_, v___x_1509_, v___x_1510_, v___x_1497_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_tail_1490_);
return v___x_1511_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1490_);
return v___x_1491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1523_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1525_, size_t v_x_1526_, size_t v_x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_object* v_cs_1536_; lean_object* v___x_1537_; size_t v___x_1538_; lean_object* v_j_1539_; lean_object* v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v_cs_1536_ = lean_ctor_get(v_x_1525_, 0);
lean_inc_ref(v_cs_1536_);
lean_dec_ref(v_x_1525_);
v___x_1537_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1538_ = lean_usize_shift_right(v_x_1526_, v_x_1527_);
v_j_1539_ = lean_usize_to_nat(v___x_1538_);
v___x_1540_ = lean_array_get_borrowed(v___x_1537_, v_cs_1536_, v_j_1539_);
v___x_1541_ = ((size_t)1ULL);
v___x_1542_ = lean_usize_shift_left(v___x_1541_, v_x_1527_);
v___x_1543_ = lean_usize_sub(v___x_1542_, v___x_1541_);
v___x_1544_ = lean_usize_land(v_x_1526_, v___x_1543_);
v___x_1545_ = ((size_t)5ULL);
v___x_1546_ = lean_usize_sub(v_x_1527_, v___x_1545_);
lean_inc(v___x_1540_);
v___x_1547_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1540_, v___x_1544_, v___x_1546_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1569_; 
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1570_);
v___x_1549_ = v___x_1547_;
v_isShared_1550_ = v_isSharedCheck_1569_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v___x_1547_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1569_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_add(v_j_1539_, v___x_1551_);
lean_dec(v_j_1539_);
v___x_1553_ = lean_array_get_size(v_cs_1536_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_nat_dec_lt(v___x_1552_, v___x_1553_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1557_; 
lean_dec(v___x_1552_);
lean_dec_ref(v_cs_1536_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1554_);
v___x_1557_ = v___x_1549_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1554_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_nat_dec_le(v___x_1553_, v___x_1553_);
if (v___x_1559_ == 0)
{
if (v___x_1555_ == 0)
{
lean_object* v___x_1561_; 
lean_dec(v___x_1552_);
lean_dec_ref(v_cs_1536_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1554_);
v___x_1561_ = v___x_1549_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1554_);
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
size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
lean_del_object(v___x_1549_);
v___x_1563_ = lean_usize_of_nat(v___x_1552_);
lean_dec(v___x_1552_);
v___x_1564_ = lean_usize_of_nat(v___x_1553_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1536_, v___x_1563_, v___x_1564_, v___x_1554_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec_ref(v_cs_1536_);
return v___x_1565_;
}
}
else
{
size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
lean_del_object(v___x_1549_);
v___x_1566_ = lean_usize_of_nat(v___x_1552_);
lean_dec(v___x_1552_);
v___x_1567_ = lean_usize_of_nat(v___x_1553_);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1536_, v___x_1566_, v___x_1567_, v___x_1554_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec_ref(v_cs_1536_);
return v___x_1568_;
}
}
}
}
else
{
lean_dec(v_j_1539_);
lean_dec_ref(v_cs_1536_);
return v___x_1547_;
}
}
else
{
lean_object* v_vs_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1592_; 
v_vs_1571_ = lean_ctor_get(v_x_1525_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1525_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1573_ = v_x_1525_;
v_isShared_1574_ = v_isSharedCheck_1592_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_vs_1571_);
lean_dec(v_x_1525_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1592_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1575_ = lean_usize_to_nat(v_x_1526_);
v___x_1576_ = lean_array_get_size(v_vs_1571_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1580_; 
lean_dec(v___x_1575_);
lean_dec_ref(v_vs_1571_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1577_);
v___x_1580_ = v___x_1573_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1577_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_le(v___x_1576_, v___x_1576_);
if (v___x_1582_ == 0)
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1584_; 
lean_dec(v___x_1575_);
lean_dec_ref(v_vs_1571_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1577_);
v___x_1584_ = v___x_1573_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1577_);
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
lean_del_object(v___x_1573_);
v___x_1586_ = lean_usize_of_nat(v___x_1575_);
lean_dec(v___x_1575_);
v___x_1587_ = lean_usize_of_nat(v___x_1576_);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1571_, v___x_1586_, v___x_1587_, v___x_1577_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec_ref(v_vs_1571_);
return v___x_1588_;
}
}
else
{
size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
lean_del_object(v___x_1573_);
v___x_1589_ = lean_usize_of_nat(v___x_1575_);
lean_dec(v___x_1575_);
v___x_1590_ = lean_usize_of_nat(v___x_1576_);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1571_, v___x_1589_, v___x_1590_, v___x_1577_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec_ref(v_vs_1571_);
return v___x_1591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
size_t v_x_10794__boxed_1604_; size_t v_x_10795__boxed_1605_; lean_object* v_res_1606_; 
v_x_10794__boxed_1604_ = lean_unbox_usize(v_x_1594_);
lean_dec(v_x_1594_);
v_x_10795__boxed_1605_ = lean_unbox_usize(v_x_1595_);
lean_dec(v_x_1595_);
v_res_1606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1593_, v_x_10794__boxed_1604_, v_x_10795__boxed_1605_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1607_, lean_object* v_start_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = lean_nat_dec_eq(v_start_1608_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v_root_1619_; lean_object* v_tail_1620_; size_t v_shift_1621_; lean_object* v_tailOff_1622_; uint8_t v___x_1623_; 
v_root_1619_ = lean_ctor_get(v_t_1607_, 0);
lean_inc_ref(v_root_1619_);
v_tail_1620_ = lean_ctor_get(v_t_1607_, 1);
lean_inc_ref(v_tail_1620_);
v_shift_1621_ = lean_ctor_get_usize(v_t_1607_, 4);
v_tailOff_1622_ = lean_ctor_get(v_t_1607_, 3);
lean_inc(v_tailOff_1622_);
lean_dec_ref(v_t_1607_);
v___x_1623_ = lean_nat_dec_le(v_tailOff_1622_, v_start_1608_);
if (v___x_1623_ == 0)
{
size_t v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v_tailOff_1622_);
v___x_1624_ = lean_usize_of_nat(v_start_1608_);
v___x_1625_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1619_, v___x_1624_, v_shift_1621_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1645_; 
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1625_, 0);
lean_dec(v_unused_1646_);
v___x_1627_ = v___x_1625_;
v_isShared_1628_ = v_isSharedCheck_1645_;
goto v_resetjp_1626_;
}
else
{
lean_dec(v___x_1625_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1645_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1629_ = lean_array_get_size(v_tail_1620_);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_nat_dec_lt(v___x_1617_, v___x_1629_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v_tail_1620_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1630_);
v___x_1633_ = v___x_1627_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1630_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
else
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_nat_dec_le(v___x_1629_, v___x_1629_);
if (v___x_1635_ == 0)
{
if (v___x_1631_ == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v_tail_1620_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1630_);
v___x_1637_ = v___x_1627_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1630_);
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
size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
lean_del_object(v___x_1627_);
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = lean_usize_of_nat(v___x_1629_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1620_, v___x_1639_, v___x_1640_, v___x_1630_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec_ref(v_tail_1620_);
return v___x_1641_;
}
}
else
{
size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1627_);
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = lean_usize_of_nat(v___x_1629_);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1620_, v___x_1642_, v___x_1643_, v___x_1630_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec_ref(v_tail_1620_);
return v___x_1644_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1620_);
return v___x_1625_;
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
lean_dec_ref(v_root_1619_);
v___x_1647_ = lean_nat_sub(v_start_1608_, v_tailOff_1622_);
lean_dec(v_tailOff_1622_);
v___x_1648_ = lean_array_get_size(v_tail_1620_);
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_nat_dec_lt(v___x_1647_, v___x_1648_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
lean_dec(v___x_1647_);
lean_dec_ref(v_tail_1620_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
return v___x_1651_;
}
else
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_nat_dec_le(v___x_1648_, v___x_1648_);
if (v___x_1652_ == 0)
{
if (v___x_1650_ == 0)
{
lean_object* v___x_1653_; 
lean_dec(v___x_1647_);
lean_dec_ref(v_tail_1620_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1649_);
return v___x_1653_;
}
else
{
size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_usize_of_nat(v___x_1647_);
lean_dec(v___x_1647_);
v___x_1655_ = lean_usize_of_nat(v___x_1648_);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1620_, v___x_1654_, v___x_1655_, v___x_1649_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec_ref(v_tail_1620_);
return v___x_1656_;
}
}
else
{
size_t v___x_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_usize_of_nat(v___x_1647_);
lean_dec(v___x_1647_);
v___x_1658_ = lean_usize_of_nat(v___x_1648_);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1620_, v___x_1657_, v___x_1658_, v___x_1649_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec_ref(v_tail_1620_);
return v___x_1659_;
}
}
}
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1607_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1661_, lean_object* v_start_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1661_, v_start_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v_start_1662_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1672_, lean_object* v_start_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_decls_1682_; lean_object* v___x_1683_; 
v_decls_1682_ = lean_ctor_get(v_lctx_1672_, 1);
lean_inc_ref(v_decls_1682_);
lean_dec_ref(v_lctx_1672_);
v___x_1683_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1682_, v_start_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1684_, lean_object* v_start_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1684_, v_start_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v_start_1685_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_lctx_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_lctx_1703_ = lean_ctor_get(v_a_1698_, 2);
lean_inc_ref(v_lctx_1703_);
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1703_, v___x_1704_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec_ref(v_a_1698_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1714_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1716_){
_start:
{
lean_object* v___f_1717_; lean_object* v___x_1718_; 
v___f_1717_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1718_ = lean_find_expr(v___f_1717_, v_e_1716_);
if (lean_obj_tag(v___x_1718_) == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = 0;
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; 
lean_dec_ref(v___x_1718_);
v___x_1720_ = 1;
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1721_);
lean_dec_ref(v_e_1721_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1727_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
v___x_1734_ = lean_apply_9(v_k_1724_, v_b_1728_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, lean_box(0));
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v_b_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1746_, uint8_t v_bi_1747_, lean_object* v_type_1748_, lean_object* v_k_1749_, uint8_t v_kind_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___f_1759_; lean_object* v___x_1760_; 
lean_inc(v___y_1753_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1759_, 0, v_k_1749_);
lean_closure_set(v___f_1759_, 1, v___y_1751_);
lean_closure_set(v___f_1759_, 2, v___y_1752_);
lean_closure_set(v___f_1759_, 3, v___y_1753_);
v___x_1760_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1746_, v_bi_1747_, v_type_1748_, v___f_1759_, v_kind_1750_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1760_) == 0)
{
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1769_, lean_object* v_bi_1770_, lean_object* v_type_1771_, lean_object* v_k_1772_, lean_object* v_kind_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
uint8_t v_bi_boxed_1782_; uint8_t v_kind_boxed_1783_; lean_object* v_res_1784_; 
v_bi_boxed_1782_ = lean_unbox(v_bi_1770_);
v_kind_boxed_1783_ = lean_unbox(v_kind_1773_);
v_res_1784_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1769_, v_bi_boxed_1782_, v_type_1771_, v_k_1772_, v_kind_boxed_1783_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1785_, lean_object* v_name_1786_, uint8_t v_bi_1787_, lean_object* v_type_1788_, lean_object* v_k_1789_, uint8_t v_kind_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1786_, v_bi_1787_, v_type_1788_, v_k_1789_, v_kind_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1800_, lean_object* v_name_1801_, lean_object* v_bi_1802_, lean_object* v_type_1803_, lean_object* v_k_1804_, lean_object* v_kind_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v_bi_boxed_1814_; uint8_t v_kind_boxed_1815_; lean_object* v_res_1816_; 
v_bi_boxed_1814_ = lean_unbox(v_bi_1802_);
v_kind_boxed_1815_ = lean_unbox(v_kind_1805_);
v_res_1816_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1800_, v_name_1801_, v_bi_boxed_1814_, v_type_1803_, v_k_1804_, v_kind_boxed_1815_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1817_, lean_object* v_e_1818_, lean_object* v___f_1819_, lean_object* v_____r_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
if (v_types_1817_ == 0)
{
lean_object* v___x_1829_; 
lean_inc_ref(v_e_1818_);
v___x_1829_ = l_Lean_Meta_isType(v_e_1818_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1840_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_unbox(v_a_1830_);
lean_dec(v_a_1830_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_del_object(v___x_1832_);
lean_dec_ref(v_e_1818_);
v___x_1835_ = lean_box(0);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc(v___y_1822_);
lean_inc_ref(v___y_1821_);
v___x_1836_ = lean_apply_9(v___f_1819_, v___x_1835_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, lean_box(0));
return v___x_1836_;
}
else
{
lean_object* v___x_1838_; 
lean_dec_ref(v___f_1819_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v_e_1818_);
v___x_1838_ = v___x_1832_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_e_1818_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v___f_1819_);
lean_dec_ref(v_e_1818_);
v_a_1841_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1829_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1829_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec_ref(v_e_1818_);
v___x_1849_ = lean_box(0);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc(v___y_1822_);
lean_inc_ref(v___y_1821_);
v___x_1850_ = lean_apply_9(v___f_1819_, v___x_1849_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, lean_box(0));
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1851_, lean_object* v_e_1852_, lean_object* v___f_1853_, lean_object* v_____r_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_types_boxed_1863_; lean_object* v_res_1864_; 
v_types_boxed_1863_ = lean_unbox(v_types_1851_);
v_res_1864_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1863_, v_e_1852_, v___f_1853_, v_____r_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1864_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1865_, uint8_t v___y_1866_){
_start:
{
if (v___y_1865_ == 0)
{
if (v___y_1866_ == 0)
{
uint8_t v___x_1867_; 
v___x_1867_ = 1;
return v___x_1867_;
}
else
{
return v___y_1865_;
}
}
else
{
return v___y_1866_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v___y_50691__boxed_1870_; uint8_t v___y_50692__boxed_1871_; uint8_t v_res_1872_; lean_object* v_r_1873_; 
v___y_50691__boxed_1870_ = lean_unbox(v___y_1868_);
v___y_50692__boxed_1871_ = lean_unbox(v___y_1869_);
v_res_1872_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_50691__boxed_1870_, v___y_50692__boxed_1871_);
v_r_1873_ = lean_box(v_res_1872_);
return v_r_1873_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_instMonadEIO(lean_box(0));
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_toApplicative_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1965_; 
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1893_ = l_StateRefT_x27_instMonad___redArg(v___x_1892_);
v_toApplicative_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1893_, 1);
lean_dec(v_unused_1966_);
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1965_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_toApplicative_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1965_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_toFunctor_1898_; lean_object* v_toSeq_1899_; lean_object* v_toSeqLeft_1900_; lean_object* v_toSeqRight_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1963_; 
v_toFunctor_1898_ = lean_ctor_get(v_toApplicative_1894_, 0);
v_toSeq_1899_ = lean_ctor_get(v_toApplicative_1894_, 2);
v_toSeqLeft_1900_ = lean_ctor_get(v_toApplicative_1894_, 3);
v_toSeqRight_1901_ = lean_ctor_get(v_toApplicative_1894_, 4);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_toApplicative_1894_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v_toApplicative_1894_, 1);
lean_dec(v_unused_1964_);
v___x_1903_ = v_toApplicative_1894_;
v_isShared_1904_ = v_isSharedCheck_1963_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_toSeqRight_1901_);
lean_inc(v_toSeqLeft_1900_);
lean_inc(v_toSeq_1899_);
lean_inc(v_toFunctor_1898_);
lean_dec(v_toApplicative_1894_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1963_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___f_1905_; lean_object* v___f_1906_; lean_object* v___f_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; lean_object* v___f_1910_; lean_object* v___f_1911_; lean_object* v___f_1912_; lean_object* v___x_1914_; 
v___f_1905_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1906_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1898_);
v___f_1907_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1907_, 0, v_toFunctor_1898_);
v___f_1908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1908_, 0, v_toFunctor_1898_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___f_1907_);
lean_ctor_set(v___x_1909_, 1, v___f_1908_);
v___f_1910_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1910_, 0, v_toSeqRight_1901_);
v___f_1911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1911_, 0, v_toSeqLeft_1900_);
v___f_1912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1912_, 0, v_toSeq_1899_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 4, v___f_1910_);
lean_ctor_set(v___x_1903_, 3, v___f_1911_);
lean_ctor_set(v___x_1903_, 2, v___f_1912_);
lean_ctor_set(v___x_1903_, 1, v___f_1905_);
lean_ctor_set(v___x_1903_, 0, v___x_1909_);
v___x_1914_ = v___x_1903_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___f_1905_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v___f_1912_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v___f_1911_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v___f_1910_);
v___x_1914_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___f_1906_);
lean_ctor_set(v___x_1896_, 0, v___x_1914_);
v___x_1916_ = v___x_1896_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___f_1906_);
v___x_1916_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v_toApplicative_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1959_; 
v___x_1917_ = l_StateRefT_x27_instMonad___redArg(v___x_1916_);
v_toApplicative_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v___x_1917_, 1);
lean_dec(v_unused_1960_);
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1959_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_toApplicative_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1959_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_toFunctor_1922_; lean_object* v_toSeq_1923_; lean_object* v_toSeqLeft_1924_; lean_object* v_toSeqRight_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1957_; 
v_toFunctor_1922_ = lean_ctor_get(v_toApplicative_1918_, 0);
v_toSeq_1923_ = lean_ctor_get(v_toApplicative_1918_, 2);
v_toSeqLeft_1924_ = lean_ctor_get(v_toApplicative_1918_, 3);
v_toSeqRight_1925_ = lean_ctor_get(v_toApplicative_1918_, 4);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_toApplicative_1918_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v_toApplicative_1918_, 1);
lean_dec(v_unused_1958_);
v___x_1927_ = v_toApplicative_1918_;
v_isShared_1928_ = v_isSharedCheck_1957_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_toSeqRight_1925_);
lean_inc(v_toSeqLeft_1924_);
lean_inc(v_toSeq_1923_);
lean_inc(v_toFunctor_1922_);
lean_dec(v_toApplicative_1918_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1957_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___f_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___f_1936_; lean_object* v___f_1937_; lean_object* v___f_1938_; lean_object* v___f_1939_; lean_object* v___x_1940_; lean_object* v___f_1941_; lean_object* v___f_1942_; lean_object* v___f_1943_; lean_object* v___x_1945_; 
v___f_1929_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1930_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1930_, 0, v___f_1929_);
v___x_1931_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1932_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1932_, 0, v___f_1930_);
lean_closure_set(v___f_1932_, 1, v___x_1931_);
v___f_1933_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1934_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1935_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1935_, 0, v___f_1933_);
lean_closure_set(v___f_1935_, 1, v___x_1934_);
v___f_1936_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1937_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1922_);
v___f_1938_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1938_, 0, v_toFunctor_1922_);
v___f_1939_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1939_, 0, v_toFunctor_1922_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___f_1938_);
lean_ctor_set(v___x_1940_, 1, v___f_1939_);
v___f_1941_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1941_, 0, v_toSeqRight_1925_);
v___f_1942_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1942_, 0, v_toSeqLeft_1924_);
v___f_1943_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1943_, 0, v_toSeq_1923_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 4, v___f_1941_);
lean_ctor_set(v___x_1927_, 3, v___f_1942_);
lean_ctor_set(v___x_1927_, 2, v___f_1943_);
lean_ctor_set(v___x_1927_, 1, v___f_1936_);
lean_ctor_set(v___x_1927_, 0, v___x_1940_);
v___x_1945_ = v___x_1927_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___f_1936_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v___f_1943_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v___f_1942_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v___f_1941_);
v___x_1945_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1947_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___f_1937_);
lean_ctor_set(v___x_1920_, 0, v___x_1945_);
v___x_1947_ = v___x_1920_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___f_1937_);
v___x_1947_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___f_1952_; lean_object* v___x_47579__overap_1953_; lean_object* v___x_1954_; 
v___x_1948_ = l_StateRefT_x27_instMonad___redArg(v___x_1947_);
v___x_1949_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1891_, v___f_1932_, v___f_1935_, v___x_1948_);
v___x_1950_ = l_Lean_instInhabitedExpr;
v___x_1951_ = l_instInhabitedOfMonad___redArg(v___x_1949_, v___x_1950_);
v___f_1952_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1952_, 0, v___x_1951_);
v___x_47579__overap_1953_ = lean_panic_fn(v___f_1952_, v_msg_1882_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc(v___y_1885_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
v___x_1954_ = lean_apply_8(v___x_47579__overap_1953_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, lean_box(0));
return v___x_1954_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderName_1977_, uint8_t v_binderInfo_1978_, lean_object* v_e_1979_, lean_object* v_binderType_1980_, lean_object* v_body_1981_, lean_object* v_t_1982_, lean_object* v_b_1983_){
_start:
{
uint8_t v___y_1985_; size_t v___x_1989_; size_t v___x_1990_; uint8_t v___x_1991_; 
v___x_1989_ = lean_ptr_addr(v_binderType_1980_);
v___x_1990_ = lean_ptr_addr(v_t_1982_);
v___x_1991_ = lean_usize_dec_eq(v___x_1989_, v___x_1990_);
if (v___x_1991_ == 0)
{
v___y_1985_ = v___x_1991_;
goto v___jp_1984_;
}
else
{
size_t v___x_1992_; size_t v___x_1993_; uint8_t v___x_1994_; 
v___x_1992_ = lean_ptr_addr(v_body_1981_);
v___x_1993_ = lean_ptr_addr(v_b_1983_);
v___x_1994_ = lean_usize_dec_eq(v___x_1992_, v___x_1993_);
v___y_1985_ = v___x_1994_;
goto v___jp_1984_;
}
v___jp_1984_:
{
if (v___y_1985_ == 0)
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Expr_lam___override(v_binderName_1977_, v_t_1982_, v_b_1983_, v_binderInfo_1978_);
return v___x_1986_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1978_, v_binderInfo_1978_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Expr_lam___override(v_binderName_1977_, v_t_1982_, v_b_1983_, v_binderInfo_1978_);
return v___x_1988_;
}
else
{
lean_dec_ref(v_b_1983_);
lean_dec_ref(v_t_1982_);
lean_dec(v_binderName_1977_);
lean_inc_ref(v_e_1979_);
return v_e_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderName_1995_, lean_object* v_binderInfo_1996_, lean_object* v_e_1997_, lean_object* v_binderType_1998_, lean_object* v_body_1999_, lean_object* v_t_2000_, lean_object* v_b_2001_){
_start:
{
uint8_t v_binderInfo_50878__boxed_2002_; lean_object* v_res_2003_; 
v_binderInfo_50878__boxed_2002_ = lean_unbox(v_binderInfo_1996_);
v_res_2003_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderName_1995_, v_binderInfo_50878__boxed_2002_, v_e_1997_, v_binderType_1998_, v_body_1999_, v_t_2000_, v_b_2001_);
lean_dec_ref(v_body_1999_);
lean_dec_ref(v_binderType_1998_);
lean_dec_ref(v_e_1997_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderName_2004_, uint8_t v_binderInfo_2005_, lean_object* v_e_2006_, lean_object* v_binderType_2007_, lean_object* v_body_2008_, lean_object* v_t_2009_, lean_object* v_b_2010_){
_start:
{
uint8_t v___y_2012_; size_t v___x_2016_; size_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = lean_ptr_addr(v_binderType_2007_);
v___x_2017_ = lean_ptr_addr(v_t_2009_);
v___x_2018_ = lean_usize_dec_eq(v___x_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
v___y_2012_ = v___x_2018_;
goto v___jp_2011_;
}
else
{
size_t v___x_2019_; size_t v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = lean_ptr_addr(v_body_2008_);
v___x_2020_ = lean_ptr_addr(v_b_2010_);
v___x_2021_ = lean_usize_dec_eq(v___x_2019_, v___x_2020_);
v___y_2012_ = v___x_2021_;
goto v___jp_2011_;
}
v___jp_2011_:
{
if (v___y_2012_ == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_Expr_forallE___override(v_binderName_2004_, v_t_2009_, v_b_2010_, v_binderInfo_2005_);
return v___x_2013_;
}
else
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2005_, v_binderInfo_2005_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Expr_forallE___override(v_binderName_2004_, v_t_2009_, v_b_2010_, v_binderInfo_2005_);
return v___x_2015_;
}
else
{
lean_dec_ref(v_b_2010_);
lean_dec_ref(v_t_2009_);
lean_dec(v_binderName_2004_);
lean_inc_ref(v_e_2006_);
return v_e_2006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderName_2022_, lean_object* v_binderInfo_2023_, lean_object* v_e_2024_, lean_object* v_binderType_2025_, lean_object* v_body_2026_, lean_object* v_t_2027_, lean_object* v_b_2028_){
_start:
{
uint8_t v_binderInfo_50912__boxed_2029_; lean_object* v_res_2030_; 
v_binderInfo_50912__boxed_2029_ = lean_unbox(v_binderInfo_2023_);
v_res_2030_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderName_2022_, v_binderInfo_50912__boxed_2029_, v_e_2024_, v_binderType_2025_, v_body_2026_, v_t_2027_, v_b_2028_);
lean_dec_ref(v_body_2026_);
lean_dec_ref(v_binderType_2025_);
lean_dec_ref(v_e_2024_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_2031_, lean_object* v_type_2032_, lean_object* v_val_2033_, lean_object* v_k_2034_, uint8_t v_nondep_2035_, uint8_t v_kind_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___f_2045_; lean_object* v___x_2046_; 
lean_inc(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
v___f_2045_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2045_, 0, v_k_2034_);
lean_closure_set(v___f_2045_, 1, v___y_2037_);
lean_closure_set(v___f_2045_, 2, v___y_2038_);
lean_closure_set(v___f_2045_, 3, v___y_2039_);
v___x_2046_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2031_, v_type_2032_, v_val_2033_, v___f_2045_, v_nondep_2035_, v_kind_2036_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2046_) == 0)
{
return v___x_2046_;
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2055_, lean_object* v_type_2056_, lean_object* v_val_2057_, lean_object* v_k_2058_, lean_object* v_nondep_2059_, lean_object* v_kind_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v_nondep_boxed_2069_; uint8_t v_kind_boxed_2070_; lean_object* v_res_2071_; 
v_nondep_boxed_2069_ = lean_unbox(v_nondep_2059_);
v_kind_boxed_2070_ = lean_unbox(v_kind_2060_);
v_res_2071_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2055_, v_type_2056_, v_val_2057_, v_k_2058_, v_nondep_boxed_2069_, v_kind_boxed_2070_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = l_Lean_instInhabitedExpr;
v___x_2074_ = lean_panic_fn(v___x_2073_, v_msg_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2075_, lean_object* v_x_2076_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_box(0);
return v___x_2077_;
}
else
{
lean_object* v_key_2078_; lean_object* v_value_2079_; lean_object* v_tail_2080_; uint8_t v___x_2081_; 
v_key_2078_ = lean_ctor_get(v_x_2076_, 0);
v_value_2079_ = lean_ctor_get(v_x_2076_, 1);
v_tail_2080_ = lean_ctor_get(v_x_2076_, 2);
v___x_2081_ = l_Lean_ExprStructEq_beq(v_key_2078_, v_a_2075_);
if (v___x_2081_ == 0)
{
v_x_2076_ = v_tail_2080_;
goto _start;
}
else
{
lean_object* v___x_2083_; 
lean_inc(v_value_2079_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_value_2079_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2084_, lean_object* v_x_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2084_, v_x_2085_);
lean_dec(v_x_2085_);
lean_dec_ref(v_a_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_buckets_2089_; lean_object* v___x_2090_; uint64_t v___x_2091_; uint64_t v___x_2092_; uint64_t v___x_2093_; uint64_t v_fold_2094_; uint64_t v___x_2095_; uint64_t v___x_2096_; uint64_t v___x_2097_; size_t v___x_2098_; size_t v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_buckets_2089_ = lean_ctor_get(v_m_2087_, 1);
v___x_2090_ = lean_array_get_size(v_buckets_2089_);
v___x_2091_ = l_Lean_ExprStructEq_hash(v_a_2088_);
v___x_2092_ = 32ULL;
v___x_2093_ = lean_uint64_shift_right(v___x_2091_, v___x_2092_);
v_fold_2094_ = lean_uint64_xor(v___x_2091_, v___x_2093_);
v___x_2095_ = 16ULL;
v___x_2096_ = lean_uint64_shift_right(v_fold_2094_, v___x_2095_);
v___x_2097_ = lean_uint64_xor(v_fold_2094_, v___x_2096_);
v___x_2098_ = lean_uint64_to_usize(v___x_2097_);
v___x_2099_ = lean_usize_of_nat(v___x_2090_);
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_sub(v___x_2099_, v___x_2100_);
v___x_2102_ = lean_usize_land(v___x_2098_, v___x_2101_);
v___x_2103_ = lean_array_uget_borrowed(v_buckets_2089_, v___x_2102_);
v___x_2104_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2088_, v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2105_, v_a_2106_);
lean_dec_ref(v_a_2106_);
lean_dec_ref(v_m_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2108_, lean_object* v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
uint8_t v___x_2110_; 
v___x_2110_ = 0;
return v___x_2110_;
}
else
{
lean_object* v_key_2111_; lean_object* v_tail_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v_fst_2115_; lean_object* v_snd_2116_; uint8_t v___x_2120_; 
v_key_2111_ = lean_ctor_get(v_x_2109_, 0);
v_tail_2112_ = lean_ctor_get(v_x_2109_, 2);
v_fst_2113_ = lean_ctor_get(v_key_2111_, 0);
v_snd_2114_ = lean_ctor_get(v_key_2111_, 1);
v_fst_2115_ = lean_ctor_get(v_a_2108_, 0);
v_snd_2116_ = lean_ctor_get(v_a_2108_, 1);
v___x_2120_ = lean_unbox(v_fst_2113_);
if (v___x_2120_ == 0)
{
uint8_t v___x_2121_; 
v___x_2121_ = lean_unbox(v_fst_2115_);
if (v___x_2121_ == 0)
{
goto v___jp_2117_;
}
else
{
v_x_2109_ = v_tail_2112_;
goto _start;
}
}
else
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_unbox(v_fst_2115_);
if (v___x_2123_ == 0)
{
v_x_2109_ = v_tail_2112_;
goto _start;
}
else
{
goto v___jp_2117_;
}
}
v___jp_2117_:
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lean_ExprStructEq_beq(v_snd_2114_, v_snd_2116_);
if (v___x_2118_ == 0)
{
v_x_2109_ = v_tail_2112_;
goto _start;
}
else
{
return v___x_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2125_, lean_object* v_x_2126_){
_start:
{
uint8_t v_res_2127_; lean_object* v_r_2128_; 
v_res_2127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2125_, v_x_2126_);
lean_dec(v_x_2126_);
lean_dec_ref(v_a_2125_);
v_r_2128_ = lean_box(v_res_2127_);
return v_r_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2129_, lean_object* v_b_2130_, lean_object* v_x_2131_){
_start:
{
if (lean_obj_tag(v_x_2131_) == 0)
{
lean_dec(v_b_2130_);
lean_dec_ref(v_a_2129_);
return v_x_2131_;
}
else
{
lean_object* v_key_2132_; lean_object* v_value_2133_; lean_object* v_tail_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2153_; 
v_key_2132_ = lean_ctor_get(v_x_2131_, 0);
v_value_2133_ = lean_ctor_get(v_x_2131_, 1);
v_tail_2134_ = lean_ctor_get(v_x_2131_, 2);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_x_2131_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2136_ = v_x_2131_;
v_isShared_2137_ = v_isSharedCheck_2153_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_tail_2134_);
lean_inc(v_value_2133_);
lean_inc(v_key_2132_);
lean_dec(v_x_2131_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2153_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_fst_2143_; lean_object* v_snd_2144_; lean_object* v_fst_2145_; lean_object* v_snd_2146_; uint8_t v___x_2150_; 
v_fst_2143_ = lean_ctor_get(v_key_2132_, 0);
v_snd_2144_ = lean_ctor_get(v_key_2132_, 1);
v_fst_2145_ = lean_ctor_get(v_a_2129_, 0);
v_snd_2146_ = lean_ctor_get(v_a_2129_, 1);
v___x_2150_ = lean_unbox(v_fst_2143_);
if (v___x_2150_ == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_unbox(v_fst_2145_);
if (v___x_2151_ == 0)
{
goto v___jp_2147_;
}
else
{
goto v___jp_2138_;
}
}
else
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_unbox(v_fst_2145_);
if (v___x_2152_ == 0)
{
goto v___jp_2138_;
}
else
{
goto v___jp_2147_;
}
}
v___jp_2138_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2129_, v_b_2130_, v_tail_2134_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 2, v___x_2139_);
v___x_2141_ = v___x_2136_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_key_2132_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_value_2133_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
v___jp_2147_:
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Lean_ExprStructEq_beq(v_snd_2144_, v_snd_2146_);
if (v___x_2148_ == 0)
{
goto v___jp_2138_;
}
else
{
lean_object* v___x_2149_; 
lean_del_object(v___x_2136_);
lean_dec(v_value_2133_);
lean_dec(v_key_2132_);
v___x_2149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2149_, 0, v_a_2129_);
lean_ctor_set(v___x_2149_, 1, v_b_2130_);
lean_ctor_set(v___x_2149_, 2, v_tail_2134_);
return v___x_2149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2154_, lean_object* v_x_2155_){
_start:
{
if (lean_obj_tag(v_x_2155_) == 0)
{
return v_x_2154_;
}
else
{
lean_object* v_key_2156_; lean_object* v_value_2157_; lean_object* v_tail_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2189_; 
v_key_2156_ = lean_ctor_get(v_x_2155_, 0);
v_value_2157_ = lean_ctor_get(v_x_2155_, 1);
v_tail_2158_ = lean_ctor_get(v_x_2155_, 2);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_x_2155_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2160_ = v_x_2155_;
v_isShared_2161_ = v_isSharedCheck_2189_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_tail_2158_);
lean_inc(v_value_2157_);
lean_inc(v_key_2156_);
lean_dec(v_x_2155_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2189_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_fst_2162_; lean_object* v_snd_2163_; lean_object* v___x_2164_; uint64_t v___y_2166_; uint8_t v___x_2186_; 
v_fst_2162_ = lean_ctor_get(v_key_2156_, 0);
v_snd_2163_ = lean_ctor_get(v_key_2156_, 1);
v___x_2164_ = lean_array_get_size(v_x_2154_);
v___x_2186_ = lean_unbox(v_fst_2162_);
if (v___x_2186_ == 0)
{
uint64_t v___x_2187_; 
v___x_2187_ = 13ULL;
v___y_2166_ = v___x_2187_;
goto v___jp_2165_;
}
else
{
uint64_t v___x_2188_; 
v___x_2188_ = 11ULL;
v___y_2166_ = v___x_2188_;
goto v___jp_2165_;
}
v___jp_2165_:
{
uint64_t v___x_2167_; uint64_t v___x_2168_; uint64_t v___x_2169_; uint64_t v___x_2170_; uint64_t v_fold_2171_; uint64_t v___x_2172_; uint64_t v___x_2173_; uint64_t v___x_2174_; size_t v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2167_ = l_Lean_ExprStructEq_hash(v_snd_2163_);
v___x_2168_ = lean_uint64_mix_hash(v___y_2166_, v___x_2167_);
v___x_2169_ = 32ULL;
v___x_2170_ = lean_uint64_shift_right(v___x_2168_, v___x_2169_);
v_fold_2171_ = lean_uint64_xor(v___x_2168_, v___x_2170_);
v___x_2172_ = 16ULL;
v___x_2173_ = lean_uint64_shift_right(v_fold_2171_, v___x_2172_);
v___x_2174_ = lean_uint64_xor(v_fold_2171_, v___x_2173_);
v___x_2175_ = lean_uint64_to_usize(v___x_2174_);
v___x_2176_ = lean_usize_of_nat(v___x_2164_);
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = lean_usize_sub(v___x_2176_, v___x_2177_);
v___x_2179_ = lean_usize_land(v___x_2175_, v___x_2178_);
v___x_2180_ = lean_array_uget_borrowed(v_x_2154_, v___x_2179_);
lean_inc(v___x_2180_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 2, v___x_2180_);
v___x_2182_ = v___x_2160_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_key_2156_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_value_2157_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_array_uset(v_x_2154_, v___x_2179_, v___x_2182_);
v_x_2154_ = v___x_2183_;
v_x_2155_ = v_tail_2158_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2190_, lean_object* v_source_2191_, lean_object* v_target_2192_){
_start:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_array_get_size(v_source_2191_);
v___x_2194_ = lean_nat_dec_lt(v_i_2190_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_dec_ref(v_source_2191_);
lean_dec(v_i_2190_);
return v_target_2192_;
}
else
{
lean_object* v_es_2195_; lean_object* v___x_2196_; lean_object* v_source_2197_; lean_object* v_target_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_es_2195_ = lean_array_fget(v_source_2191_, v_i_2190_);
v___x_2196_ = lean_box(0);
v_source_2197_ = lean_array_fset(v_source_2191_, v_i_2190_, v___x_2196_);
v_target_2198_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2192_, v_es_2195_);
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_add(v_i_2190_, v___x_2199_);
lean_dec(v_i_2190_);
v_i_2190_ = v___x_2200_;
v_source_2191_ = v_source_2197_;
v_target_2192_ = v_target_2198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2202_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v_nbuckets_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2203_ = lean_array_get_size(v_data_2202_);
v___x_2204_ = lean_unsigned_to_nat(2u);
v_nbuckets_2205_ = lean_nat_mul(v___x_2203_, v___x_2204_);
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_mk_array(v_nbuckets_2205_, v___x_2207_);
v___x_2209_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2206_, v_data_2202_, v___x_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2210_, lean_object* v_a_2211_, lean_object* v_b_2212_){
_start:
{
lean_object* v_size_2213_; lean_object* v_buckets_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2265_; 
v_size_2213_ = lean_ctor_get(v_m_2210_, 0);
v_buckets_2214_ = lean_ctor_get(v_m_2210_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_m_2210_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2216_ = v_m_2210_;
v_isShared_2217_ = v_isSharedCheck_2265_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_buckets_2214_);
lean_inc(v_size_2213_);
lean_dec(v_m_2210_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2265_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_fst_2218_; lean_object* v_snd_2219_; lean_object* v___x_2220_; uint64_t v___y_2222_; uint8_t v___x_2262_; 
v_fst_2218_ = lean_ctor_get(v_a_2211_, 0);
v_snd_2219_ = lean_ctor_get(v_a_2211_, 1);
v___x_2220_ = lean_array_get_size(v_buckets_2214_);
v___x_2262_ = lean_unbox(v_fst_2218_);
if (v___x_2262_ == 0)
{
uint64_t v___x_2263_; 
v___x_2263_ = 13ULL;
v___y_2222_ = v___x_2263_;
goto v___jp_2221_;
}
else
{
uint64_t v___x_2264_; 
v___x_2264_ = 11ULL;
v___y_2222_ = v___x_2264_;
goto v___jp_2221_;
}
v___jp_2221_:
{
uint64_t v___x_2223_; uint64_t v___x_2224_; uint64_t v___x_2225_; uint64_t v___x_2226_; uint64_t v_fold_2227_; uint64_t v___x_2228_; uint64_t v___x_2229_; uint64_t v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; lean_object* v_bkt_2236_; uint8_t v___x_2237_; 
v___x_2223_ = l_Lean_ExprStructEq_hash(v_snd_2219_);
v___x_2224_ = lean_uint64_mix_hash(v___y_2222_, v___x_2223_);
v___x_2225_ = 32ULL;
v___x_2226_ = lean_uint64_shift_right(v___x_2224_, v___x_2225_);
v_fold_2227_ = lean_uint64_xor(v___x_2224_, v___x_2226_);
v___x_2228_ = 16ULL;
v___x_2229_ = lean_uint64_shift_right(v_fold_2227_, v___x_2228_);
v___x_2230_ = lean_uint64_xor(v_fold_2227_, v___x_2229_);
v___x_2231_ = lean_uint64_to_usize(v___x_2230_);
v___x_2232_ = lean_usize_of_nat(v___x_2220_);
v___x_2233_ = ((size_t)1ULL);
v___x_2234_ = lean_usize_sub(v___x_2232_, v___x_2233_);
v___x_2235_ = lean_usize_land(v___x_2231_, v___x_2234_);
v_bkt_2236_ = lean_array_uget_borrowed(v_buckets_2214_, v___x_2235_);
v___x_2237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2211_, v_bkt_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v_size_x27_2239_; lean_object* v___x_2240_; lean_object* v_buckets_x27_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2238_ = lean_unsigned_to_nat(1u);
v_size_x27_2239_ = lean_nat_add(v_size_2213_, v___x_2238_);
lean_dec(v_size_2213_);
lean_inc(v_bkt_2236_);
v___x_2240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2211_);
lean_ctor_set(v___x_2240_, 1, v_b_2212_);
lean_ctor_set(v___x_2240_, 2, v_bkt_2236_);
v_buckets_x27_2241_ = lean_array_uset(v_buckets_2214_, v___x_2235_, v___x_2240_);
v___x_2242_ = lean_unsigned_to_nat(4u);
v___x_2243_ = lean_nat_mul(v_size_x27_2239_, v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(3u);
v___x_2245_ = lean_nat_div(v___x_2243_, v___x_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_array_get_size(v_buckets_x27_2241_);
v___x_2247_ = lean_nat_dec_le(v___x_2245_, v___x_2246_);
lean_dec(v___x_2245_);
if (v___x_2247_ == 0)
{
lean_object* v_val_2248_; lean_object* v___x_2250_; 
v_val_2248_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2241_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v_val_2248_);
lean_ctor_set(v___x_2216_, 0, v_size_x27_2239_);
v___x_2250_ = v___x_2216_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_size_x27_2239_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_val_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v___x_2253_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v_buckets_x27_2241_);
lean_ctor_set(v___x_2216_, 0, v_size_x27_2239_);
v___x_2253_ = v___x_2216_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_size_x27_2239_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_buckets_x27_2241_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v_buckets_x27_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
lean_inc(v_bkt_2236_);
v___x_2255_ = lean_box(0);
v_buckets_x27_2256_ = lean_array_uset(v_buckets_2214_, v___x_2235_, v___x_2255_);
v___x_2257_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2211_, v_b_2212_, v_bkt_2236_);
v___x_2258_ = lean_array_uset(v_buckets_x27_2256_, v___x_2235_, v___x_2257_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v___x_2258_);
v___x_2260_ = v___x_2216_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_size_2213_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2266_, lean_object* v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2267_) == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_box(0);
return v___x_2268_;
}
else
{
lean_object* v_key_2269_; lean_object* v_value_2270_; lean_object* v_tail_2271_; lean_object* v_fst_2272_; lean_object* v_snd_2273_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; uint8_t v___x_2280_; 
v_key_2269_ = lean_ctor_get(v_x_2267_, 0);
v_value_2270_ = lean_ctor_get(v_x_2267_, 1);
v_tail_2271_ = lean_ctor_get(v_x_2267_, 2);
v_fst_2272_ = lean_ctor_get(v_key_2269_, 0);
v_snd_2273_ = lean_ctor_get(v_key_2269_, 1);
v_fst_2274_ = lean_ctor_get(v_a_2266_, 0);
v_snd_2275_ = lean_ctor_get(v_a_2266_, 1);
v___x_2280_ = lean_unbox(v_fst_2272_);
if (v___x_2280_ == 0)
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_unbox(v_fst_2274_);
if (v___x_2281_ == 0)
{
goto v___jp_2276_;
}
else
{
v_x_2267_ = v_tail_2271_;
goto _start;
}
}
else
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_unbox(v_fst_2274_);
if (v___x_2283_ == 0)
{
v_x_2267_ = v_tail_2271_;
goto _start;
}
else
{
goto v___jp_2276_;
}
}
v___jp_2276_:
{
uint8_t v___x_2277_; 
v___x_2277_ = l_Lean_ExprStructEq_beq(v_snd_2273_, v_snd_2275_);
if (v___x_2277_ == 0)
{
v_x_2267_ = v_tail_2271_;
goto _start;
}
else
{
lean_object* v___x_2279_; 
lean_inc(v_value_2270_);
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_value_2270_);
return v___x_2279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2285_, lean_object* v_x_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2285_, v_x_2286_);
lean_dec(v_x_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_buckets_2290_; lean_object* v_fst_2291_; lean_object* v_snd_2292_; lean_object* v___x_2293_; uint64_t v___y_2295_; uint8_t v___x_2311_; 
v_buckets_2290_ = lean_ctor_get(v_m_2288_, 1);
v_fst_2291_ = lean_ctor_get(v_a_2289_, 0);
v_snd_2292_ = lean_ctor_get(v_a_2289_, 1);
v___x_2293_ = lean_array_get_size(v_buckets_2290_);
v___x_2311_ = lean_unbox(v_fst_2291_);
if (v___x_2311_ == 0)
{
uint64_t v___x_2312_; 
v___x_2312_ = 13ULL;
v___y_2295_ = v___x_2312_;
goto v___jp_2294_;
}
else
{
uint64_t v___x_2313_; 
v___x_2313_ = 11ULL;
v___y_2295_ = v___x_2313_;
goto v___jp_2294_;
}
v___jp_2294_:
{
uint64_t v___x_2296_; uint64_t v___x_2297_; uint64_t v___x_2298_; uint64_t v___x_2299_; uint64_t v_fold_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; uint64_t v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2296_ = l_Lean_ExprStructEq_hash(v_snd_2292_);
v___x_2297_ = lean_uint64_mix_hash(v___y_2295_, v___x_2296_);
v___x_2298_ = 32ULL;
v___x_2299_ = lean_uint64_shift_right(v___x_2297_, v___x_2298_);
v_fold_2300_ = lean_uint64_xor(v___x_2297_, v___x_2299_);
v___x_2301_ = 16ULL;
v___x_2302_ = lean_uint64_shift_right(v_fold_2300_, v___x_2301_);
v___x_2303_ = lean_uint64_xor(v_fold_2300_, v___x_2302_);
v___x_2304_ = lean_uint64_to_usize(v___x_2303_);
v___x_2305_ = lean_usize_of_nat(v___x_2293_);
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = lean_usize_sub(v___x_2305_, v___x_2306_);
v___x_2308_ = lean_usize_land(v___x_2304_, v___x_2307_);
v___x_2309_ = lean_array_uget_borrowed(v_buckets_2290_, v___x_2308_);
v___x_2310_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2289_, v___x_2309_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2314_, v_a_2315_);
lean_dec_ref(v_a_2315_);
lean_dec_ref(v_m_2314_);
return v_res_2316_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2317_; lean_object* v_dummy_2318_; 
v___x_2317_ = lean_box(0);
v_dummy_2318_ = l_Lean_Expr_sort___override(v___x_2317_);
return v_dummy_2318_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2319_, lean_object* v_fst_2320_, lean_object* v_fvars_2321_, lean_object* v_a_2322_, lean_object* v_b_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_a_2333_; uint8_t v___x_2337_; 
v___x_2337_ = lean_nat_dec_lt(v_a_2322_, v_upperBound_2319_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_dec(v_a_2322_);
lean_dec(v_fvars_2321_);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_b_2323_);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v_binderInfo_2341_; uint8_t v___x_2342_; 
v___x_2339_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2340_ = lean_array_get_borrowed(v___x_2339_, v_fst_2320_, v_a_2322_);
v_binderInfo_2341_ = lean_ctor_get_uint8(v___x_2340_, sizeof(void*)*2);
v___x_2342_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2341_);
if (v___x_2342_ == 0)
{
v_a_2333_ = v_b_2323_;
goto v___jp_2332_;
}
else
{
uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2343_ = 0;
v___x_2344_ = l_Lean_instInhabitedExpr;
v___x_2345_ = lean_array_get_borrowed(v___x_2344_, v_b_2323_, v_a_2322_);
lean_inc(v___x_2345_);
lean_inc(v_fvars_2321_);
v___x_2346_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2321_, v___x_2345_, v___x_2343_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = lean_array_set(v_b_2323_, v_a_2322_, v_a_2347_);
v_a_2333_ = v___x_2348_;
goto v___jp_2332_;
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v_b_2323_);
lean_dec(v_a_2322_);
lean_dec(v_fvars_2321_);
v_a_2349_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2346_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2346_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
v___jp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_unsigned_to_nat(1u);
v___x_2335_ = lean_nat_add(v_a_2322_, v___x_2334_);
lean_dec(v_a_2322_);
v_a_2322_ = v___x_2335_;
v_b_2323_ = v_a_2333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2357_, size_t v_sz_2358_, size_t v_i_2359_, lean_object* v_bs_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_usize_dec_lt(v_i_2359_, v_sz_2358_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; 
lean_dec(v_fvars_2357_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v_bs_2360_);
return v___x_2370_;
}
else
{
uint8_t v___x_2371_; lean_object* v_v_2372_; lean_object* v___x_2373_; 
v___x_2371_ = 0;
v_v_2372_ = lean_array_uget_borrowed(v_bs_2360_, v_i_2359_);
lean_inc(v_v_2372_);
lean_inc(v_fvars_2357_);
v___x_2373_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2357_, v_v_2372_, v___x_2371_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v_bs_x27_2376_; size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = lean_unsigned_to_nat(0u);
v_bs_x27_2376_ = lean_array_uset(v_bs_2360_, v_i_2359_, v___x_2375_);
v___x_2377_ = ((size_t)1ULL);
v___x_2378_ = lean_usize_add(v_i_2359_, v___x_2377_);
v___x_2379_ = lean_array_uset(v_bs_x27_2376_, v_i_2359_, v_a_2374_);
v_i_2359_ = v___x_2378_;
v_bs_2360_ = v___x_2379_;
goto _start;
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v_bs_2360_);
lean_dec(v_fvars_2357_);
v_a_2381_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2373_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2373_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2389_, lean_object* v_f_2390_, lean_object* v_args_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
uint8_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = 0;
lean_inc_ref(v_f_2390_);
lean_inc(v_fvars_2389_);
v___x_2401_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2389_, v_f_2390_, v___x_2400_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2401_) == 0)
{
uint8_t v_implicits_2402_; 
v_implicits_2402_ = lean_ctor_get_uint8(v_a_2392_, 2);
if (v_implicits_2402_ == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; 
v_a_2403_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2401_);
lean_inc(v_a_2398_);
lean_inc_ref(v_a_2397_);
lean_inc(v_a_2396_);
lean_inc_ref(v_a_2395_);
v___x_2404_ = lean_infer_type(v_f_2390_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2404_);
v___x_2406_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2405_, v_args_2391_, v___x_2400_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v_fst_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v_fst_2408_ = lean_ctor_get(v_a_2407_, 0);
lean_inc(v_fst_2408_);
lean_dec(v_a_2407_);
v___x_2409_ = lean_array_get_size(v_args_2391_);
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2409_, v_fst_2408_, v_fvars_2389_, v___x_2410_, v_args_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_fst_2408_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2420_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = l_Lean_mkAppN(v_a_2403_, v_a_2412_);
lean_dec(v_a_2412_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2418_ = v___x_2414_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_a_2403_);
v_a_2421_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2411_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2411_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_a_2403_);
lean_dec_ref(v_args_2391_);
lean_dec(v_fvars_2389_);
v_a_2429_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2406_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2406_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_dec(v_a_2403_);
lean_dec_ref(v_args_2391_);
lean_dec(v_fvars_2389_);
return v___x_2404_;
}
}
else
{
lean_object* v_a_2437_; size_t v_sz_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v_f_2390_);
v_a_2437_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2437_);
lean_dec_ref(v___x_2401_);
v_sz_2438_ = lean_array_size(v_args_2391_);
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2389_, v_sz_2438_, v___x_2439_, v_args_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2449_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = l_Lean_mkAppN(v_a_2437_, v_a_2441_);
lean_dec(v_a_2441_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2445_);
v___x_2447_ = v___x_2443_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec(v_a_2437_);
v_a_2450_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2440_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2440_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2391_);
lean_dec_ref(v_f_2390_);
lean_dec(v_fvars_2389_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2458_, lean_object* v_f_2459_, lean_object* v_args_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2458_, v_f_2459_, v_args_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2470_, lean_object* v_b_2471_, uint8_t v___x_2472_, lean_object* v_mk_2473_, lean_object* v_a_2474_, lean_object* v_x_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_inc_ref(v_x_2475_);
v___x_2484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_x_2475_);
lean_ctor_set(v___x_2484_, 1, v_fvars_2470_);
v___x_2485_ = lean_expr_instantiate1(v_b_2471_, v_x_2475_);
v___x_2486_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2484_, v___x_2485_, v___x_2472_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2486_) == 0)
{
uint8_t v_lift_2487_; 
v_lift_2487_ = lean_ctor_get_uint8(v___y_2476_, 10);
if (v_lift_2487_ == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2500_; 
v_a_2488_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2490_ = v___x_2486_;
v_isShared_2491_ = v_isSharedCheck_2500_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2486_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2500_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = lean_mk_empty_array_with_capacity(v___x_2492_);
v___x_2494_ = lean_array_push(v___x_2493_, v_x_2475_);
v___x_2495_ = lean_expr_abstract(v_a_2488_, v___x_2494_);
lean_dec_ref(v___x_2494_);
lean_dec(v_a_2488_);
v___x_2496_ = lean_apply_2(v_mk_2473_, v_a_2474_, v___x_2495_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2496_);
v___x_2498_ = v___x_2490_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_a_2501_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2501_);
lean_dec_ref(v___x_2486_);
v___x_2502_ = l_Lean_Expr_fvarId_x21(v_x_2475_);
v___x_2503_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2502_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2517_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2508_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2504_, v_a_2501_);
lean_dec(v_a_2504_);
v___x_2509_ = lean_unsigned_to_nat(1u);
v___x_2510_ = lean_mk_empty_array_with_capacity(v___x_2509_);
v___x_2511_ = lean_array_push(v___x_2510_, v_x_2475_);
v___x_2512_ = lean_expr_abstract(v___x_2508_, v___x_2511_);
lean_dec_ref(v___x_2511_);
lean_dec_ref(v___x_2508_);
v___x_2513_ = lean_apply_2(v_mk_2473_, v_a_2474_, v___x_2512_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2513_);
v___x_2515_ = v___x_2506_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_a_2501_);
lean_dec_ref(v_x_2475_);
lean_dec_ref(v_a_2474_);
lean_dec_ref(v_mk_2473_);
v_a_2518_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2503_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2503_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2475_);
lean_dec_ref(v_a_2474_);
lean_dec_ref(v_mk_2473_);
return v___x_2486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2526_, lean_object* v_b_2527_, lean_object* v___x_2528_, lean_object* v_mk_2529_, lean_object* v_a_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
uint8_t v___x_51502__boxed_2540_; lean_object* v_res_2541_; 
v___x_51502__boxed_2540_ = lean_unbox(v___x_2528_);
v_res_2541_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2526_, v_b_2527_, v___x_51502__boxed_2540_, v_mk_2529_, v_a_2530_, v_x_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec_ref(v_b_2527_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2542_, lean_object* v_n_2543_, lean_object* v_t_2544_, lean_object* v_b_2545_, uint8_t v_i_2546_, lean_object* v_mk_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
uint8_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = 0;
lean_inc(v_fvars_2542_);
v___x_2557_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2542_, v_t_2544_, v___x_2556_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2557_) == 0)
{
uint8_t v_underBinder_2558_; 
v_underBinder_2558_ = lean_ctor_get_uint8(v_a_2548_, 4);
if (v_underBinder_2558_ == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_n_2543_);
lean_dec(v_fvars_2542_);
v_a_2559_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2561_ = v___x_2557_;
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2557_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2563_ = lean_apply_2(v_mk_2547_, v_a_2559_, v_b_2545_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2569_; lean_object* v___f_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; 
v_a_2568_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___x_2557_);
v___x_2569_ = lean_box(v___x_2556_);
lean_inc(v_a_2568_);
v___f_2570_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2570_, 0, v_fvars_2542_);
lean_closure_set(v___f_2570_, 1, v_b_2545_);
lean_closure_set(v___f_2570_, 2, v___x_2569_);
lean_closure_set(v___f_2570_, 3, v_mk_2547_);
lean_closure_set(v___f_2570_, 4, v_a_2568_);
v___x_2571_ = 0;
v___x_2572_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2543_, v_i_2546_, v_a_2568_, v___f_2570_, v___x_2571_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
return v___x_2572_;
}
}
else
{
lean_dec_ref(v_mk_2547_);
lean_dec_ref(v_b_2545_);
lean_dec(v_n_2543_);
lean_dec(v_fvars_2542_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2573_, lean_object* v_n_2574_, lean_object* v_t_2575_, lean_object* v_b_2576_, lean_object* v_i_2577_, lean_object* v_mk_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
uint8_t v_i_boxed_2587_; lean_object* v_res_2588_; 
v_i_boxed_2587_ = lean_unbox(v_i_2577_);
v_res_2588_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2573_, v_n_2574_, v_t_2575_, v_b_2576_, v_i_boxed_2587_, v_mk_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2589_, lean_object* v_e_2590_, lean_object* v_topLevel_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
uint8_t v_topLevel_boxed_2600_; lean_object* v_res_2601_; 
v_topLevel_boxed_2600_ = lean_unbox(v_topLevel_2591_);
v_res_2601_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2589_, v_e_2590_, v_topLevel_boxed_2600_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
return v_res_2601_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2606_ = lean_unsigned_to_nat(27u);
v___x_2607_ = lean_unsigned_to_nat(1940u);
v___x_2608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2610_ = l_mkPanicMessageWithDecl(v___x_2609_, v___x_2608_, v___x_2607_, v___x_2606_, v___x_2605_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2611_, lean_object* v_fvars_2612_, lean_object* v_b_2613_, uint8_t v___x_2614_, lean_object* v_e_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, uint8_t v_isLet_2618_, uint8_t v_topLevel_2619_, lean_object* v_x_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
if (v_fst_2611_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_inc_ref(v_x_2620_);
v___x_2629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_x_2620_);
lean_ctor_set(v___x_2629_, 1, v_fvars_2612_);
v___x_2630_ = lean_expr_instantiate1(v_b_2613_, v_x_2620_);
v___x_2631_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2629_, v___x_2630_, v___x_2614_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2631_) == 0)
{
if (lean_obj_tag(v_e_2615_) == 8)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2667_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2667_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2667_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_declName_2636_; lean_object* v_type_2637_; lean_object* v_value_2638_; lean_object* v_body_2639_; uint8_t v_nondep_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___y_2646_; size_t v___x_2661_; size_t v___x_2662_; uint8_t v___x_2663_; 
v_declName_2636_ = lean_ctor_get(v_e_2615_, 0);
v_type_2637_ = lean_ctor_get(v_e_2615_, 1);
v_value_2638_ = lean_ctor_get(v_e_2615_, 2);
v_body_2639_ = lean_ctor_get(v_e_2615_, 3);
v_nondep_2640_ = lean_ctor_get_uint8(v_e_2615_, sizeof(void*)*4 + 8);
v___x_2641_ = lean_unsigned_to_nat(1u);
v___x_2642_ = lean_mk_empty_array_with_capacity(v___x_2641_);
v___x_2643_ = lean_array_push(v___x_2642_, v_x_2620_);
v___x_2644_ = lean_expr_abstract(v_a_2632_, v___x_2643_);
lean_dec_ref(v___x_2643_);
lean_dec(v_a_2632_);
v___x_2661_ = lean_ptr_addr(v_type_2637_);
v___x_2662_ = lean_ptr_addr(v_a_2616_);
v___x_2663_ = lean_usize_dec_eq(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
v___y_2646_ = v___x_2663_;
goto v___jp_2645_;
}
else
{
size_t v___x_2664_; size_t v___x_2665_; uint8_t v___x_2666_; 
v___x_2664_ = lean_ptr_addr(v_value_2638_);
v___x_2665_ = lean_ptr_addr(v_a_2617_);
v___x_2666_ = lean_usize_dec_eq(v___x_2664_, v___x_2665_);
v___y_2646_ = v___x_2666_;
goto v___jp_2645_;
}
v___jp_2645_:
{
if (v___y_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
lean_inc(v_declName_2636_);
lean_dec_ref(v_e_2615_);
v___x_2647_ = l_Lean_Expr_letE___override(v_declName_2636_, v_a_2616_, v_a_2617_, v___x_2644_, v_nondep_2640_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2647_);
v___x_2649_ = v___x_2634_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
else
{
size_t v___x_2651_; size_t v___x_2652_; uint8_t v___x_2653_; 
v___x_2651_ = lean_ptr_addr(v_body_2639_);
v___x_2652_ = lean_ptr_addr(v___x_2644_);
v___x_2653_ = lean_usize_dec_eq(v___x_2651_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_inc(v_declName_2636_);
lean_dec_ref(v_e_2615_);
v___x_2654_ = l_Lean_Expr_letE___override(v_declName_2636_, v_a_2616_, v_a_2617_, v___x_2644_, v_nondep_2640_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2654_);
v___x_2656_ = v___x_2634_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
else
{
lean_object* v___x_2659_; 
lean_dec_ref(v___x_2644_);
lean_dec_ref(v_a_2617_);
lean_dec_ref(v_a_2616_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_e_2615_);
v___x_2659_ = v___x_2634_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_e_2615_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
else
{
lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v_x_2620_);
lean_dec_ref(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec_ref(v_e_2615_);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; 
v_unused_2677_ = lean_ctor_get(v___x_2631_, 0);
lean_dec(v_unused_2677_);
v___x_2669_ = v___x_2631_;
v_isShared_2670_ = v_isSharedCheck_2676_;
goto v_resetjp_2668_;
}
else
{
lean_dec(v___x_2631_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2676_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2672_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2671_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2672_);
v___x_2674_ = v___x_2669_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_dec_ref(v_x_2620_);
lean_dec_ref(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec_ref(v_e_2615_);
return v___x_2631_;
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec_ref(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec_ref(v_e_2615_);
v___x_2678_ = l_Lean_Expr_fvarId_x21(v_x_2620_);
lean_inc_ref(v___y_2624_);
v___x_2679_ = l_Lean_FVarId_getDecl___redArg(v___x_2678_, v___y_2624_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2679_);
v___x_2681_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2680_, v_isLet_2618_, v___y_2621_, v___y_2623_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec_ref(v___x_2681_);
v___x_2682_ = lean_expr_instantiate1(v_b_2613_, v_x_2620_);
lean_dec_ref(v_x_2620_);
v___x_2683_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2612_, v___x_2682_, v_topLevel_2619_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2683_;
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v_x_2620_);
lean_dec(v_fvars_2612_);
v_a_2684_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2681_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2681_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref(v_x_2620_);
lean_dec(v_fvars_2612_);
v_a_2692_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2679_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2679_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2700_ = _args[0];
lean_object* v_fvars_2701_ = _args[1];
lean_object* v_b_2702_ = _args[2];
lean_object* v___x_2703_ = _args[3];
lean_object* v_e_2704_ = _args[4];
lean_object* v_a_2705_ = _args[5];
lean_object* v_a_2706_ = _args[6];
lean_object* v_isLet_2707_ = _args[7];
lean_object* v_topLevel_2708_ = _args[8];
lean_object* v_x_2709_ = _args[9];
lean_object* v___y_2710_ = _args[10];
lean_object* v___y_2711_ = _args[11];
lean_object* v___y_2712_ = _args[12];
lean_object* v___y_2713_ = _args[13];
lean_object* v___y_2714_ = _args[14];
lean_object* v___y_2715_ = _args[15];
lean_object* v___y_2716_ = _args[16];
lean_object* v___y_2717_ = _args[17];
_start:
{
uint8_t v_fst_51647__boxed_2718_; uint8_t v___x_51648__boxed_2719_; uint8_t v_isLet_boxed_2720_; uint8_t v_topLevel_boxed_2721_; lean_object* v_res_2722_; 
v_fst_51647__boxed_2718_ = lean_unbox(v_fst_2700_);
v___x_51648__boxed_2719_ = lean_unbox(v___x_2703_);
v_isLet_boxed_2720_ = lean_unbox(v_isLet_2707_);
v_topLevel_boxed_2721_ = lean_unbox(v_topLevel_2708_);
v_res_2722_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_51647__boxed_2718_, v_fvars_2701_, v_b_2702_, v___x_51648__boxed_2719_, v_e_2704_, v_a_2705_, v_a_2706_, v_isLet_boxed_2720_, v_topLevel_boxed_2721_, v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec_ref(v_b_2702_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2723_, lean_object* v_e_2724_, uint8_t v_isLet_2725_, lean_object* v_n_2726_, lean_object* v_t_2727_, lean_object* v_v_2728_, lean_object* v_b_2729_, uint8_t v_topLevel_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; uint8_t v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = 0;
lean_inc(v_fvars_2723_);
v___x_2754_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2723_, v_t_2727_, v___x_2753_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2873_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2873_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2873_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; 
lean_inc(v_fvars_2723_);
v___x_2759_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2723_, v_v_2728_, v___x_2753_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2872_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2872_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2872_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
uint8_t v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; uint8_t v___y_2768_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v_descend_2812_; uint8_t v_underBinder_2813_; uint8_t v_usedOnly_2814_; uint8_t v_merge_2815_; uint8_t v_lift_2816_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; uint8_t v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; uint8_t v___y_2854_; 
v_descend_2812_ = lean_ctor_get_uint8(v_a_2731_, 3);
v_underBinder_2813_ = lean_ctor_get_uint8(v_a_2731_, 4);
v_usedOnly_2814_ = lean_ctor_get_uint8(v_a_2731_, 5);
v_merge_2815_ = lean_ctor_get_uint8(v_a_2731_, 6);
v_lift_2816_ = lean_ctor_get_uint8(v_a_2731_, 10);
if (v_usedOnly_2814_ == 0)
{
v___y_2854_ = v___x_2753_;
goto v___jp_2853_;
}
else
{
uint8_t v___x_2870_; 
v___x_2870_ = l_Lean_Expr_hasLooseBVars(v_b_2729_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; 
lean_del_object(v___x_2762_);
lean_dec(v_a_2760_);
lean_del_object(v___x_2757_);
lean_dec(v_a_2755_);
lean_dec(v_n_2726_);
lean_dec_ref(v_e_2724_);
v___x_2871_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2723_, v_b_2729_, v_topLevel_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
return v___x_2871_;
}
else
{
v___y_2854_ = v___x_2753_;
goto v___jp_2853_;
}
}
v___jp_2764_:
{
if (v___y_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
lean_dec_ref(v___y_2766_);
lean_dec_ref(v_e_2724_);
v___x_2769_ = l_Lean_Expr_letE___override(v___y_2767_, v_a_2755_, v_a_2760_, v_b_2729_, v___y_2765_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2769_);
v___x_2771_ = v___x_2762_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
size_t v___x_2773_; size_t v___x_2774_; uint8_t v___x_2775_; 
v___x_2773_ = lean_ptr_addr(v___y_2766_);
lean_dec_ref(v___y_2766_);
v___x_2774_ = lean_ptr_addr(v_b_2729_);
v___x_2775_ = lean_usize_dec_eq(v___x_2773_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
lean_dec_ref(v_e_2724_);
v___x_2776_ = l_Lean_Expr_letE___override(v___y_2767_, v_a_2755_, v_a_2760_, v_b_2729_, v___y_2765_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2776_);
v___x_2778_ = v___x_2762_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
else
{
lean_object* v___x_2781_; 
lean_dec(v___y_2767_);
lean_dec(v_a_2760_);
lean_dec(v_a_2755_);
lean_dec_ref(v_b_2729_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_e_2724_);
v___x_2781_ = v___x_2762_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_e_2724_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
v___jp_2783_:
{
if (lean_obj_tag(v_e_2724_) == 8)
{
lean_object* v_declName_2784_; lean_object* v_type_2785_; lean_object* v_value_2786_; lean_object* v_body_2787_; uint8_t v_nondep_2788_; size_t v___x_2789_; size_t v___x_2790_; uint8_t v___x_2791_; 
lean_del_object(v___x_2757_);
v_declName_2784_ = lean_ctor_get(v_e_2724_, 0);
v_type_2785_ = lean_ctor_get(v_e_2724_, 1);
v_value_2786_ = lean_ctor_get(v_e_2724_, 2);
v_body_2787_ = lean_ctor_get(v_e_2724_, 3);
v_nondep_2788_ = lean_ctor_get_uint8(v_e_2724_, sizeof(void*)*4 + 8);
v___x_2789_ = lean_ptr_addr(v_type_2785_);
v___x_2790_ = lean_ptr_addr(v_a_2755_);
v___x_2791_ = lean_usize_dec_eq(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_inc(v_declName_2784_);
lean_inc_ref(v_body_2787_);
v___y_2765_ = v_nondep_2788_;
v___y_2766_ = v_body_2787_;
v___y_2767_ = v_declName_2784_;
v___y_2768_ = v___x_2791_;
goto v___jp_2764_;
}
else
{
size_t v___x_2792_; size_t v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = lean_ptr_addr(v_value_2786_);
v___x_2793_ = lean_ptr_addr(v_a_2760_);
v___x_2794_ = lean_usize_dec_eq(v___x_2792_, v___x_2793_);
lean_inc(v_declName_2784_);
lean_inc_ref(v_body_2787_);
v___y_2765_ = v_nondep_2788_;
v___y_2766_ = v_body_2787_;
v___y_2767_ = v_declName_2784_;
v___y_2768_ = v___x_2794_;
goto v___jp_2764_;
}
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
lean_del_object(v___x_2762_);
lean_dec(v_a_2760_);
lean_dec(v_a_2755_);
lean_dec_ref(v_b_2729_);
lean_dec_ref(v_e_2724_);
v___x_2795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2796_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2795_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2796_);
v___x_2798_ = v___x_2757_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
v___jp_2800_:
{
uint8_t v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = 0;
v___x_2811_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2802_, v_a_2755_, v_a_2760_, v___y_2801_, v___x_2753_, v___x_2810_, v___y_2808_, v___y_2807_, v___y_2804_, v___y_2809_, v___y_2806_, v___y_2805_, v___y_2803_);
return v___x_2811_;
}
v___jp_2817_:
{
if (v_underBinder_2813_ == 0)
{
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
goto v___jp_2783_;
}
else
{
if (v_descend_2812_ == 0)
{
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
goto v___jp_2783_;
}
else
{
lean_del_object(v___x_2762_);
lean_del_object(v___x_2757_);
lean_dec_ref(v_b_2729_);
lean_dec_ref(v_e_2724_);
v___y_2801_ = v___y_2818_;
v___y_2802_ = v___y_2819_;
v___y_2803_ = v___y_2821_;
v___y_2804_ = v___y_2820_;
v___y_2805_ = v___y_2822_;
v___y_2806_ = v___y_2824_;
v___y_2807_ = v___y_2823_;
v___y_2808_ = v___y_2825_;
v___y_2809_ = v___y_2826_;
goto v___jp_2800_;
}
}
}
v___jp_2827_:
{
lean_object* v___x_2836_; 
lean_inc(v_a_2760_);
lean_inc(v_a_2755_);
v___x_2836_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2723_, v_n_2726_, v_a_2755_, v_a_2760_, v___y_2829_, v___y_2831_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___f_2843_; uint8_t v___x_2844_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref(v___x_2836_);
v_fst_2838_ = lean_ctor_get(v_a_2837_, 0);
lean_inc(v_fst_2838_);
v_snd_2839_ = lean_ctor_get(v_a_2837_, 1);
lean_inc(v_snd_2839_);
lean_dec(v_a_2837_);
v___x_2840_ = lean_box(v___x_2753_);
v___x_2841_ = lean_box(v_isLet_2725_);
v___x_2842_ = lean_box(v_topLevel_2730_);
lean_inc(v_a_2760_);
lean_inc(v_a_2755_);
lean_inc_ref(v_e_2724_);
lean_inc_ref(v_b_2729_);
lean_inc(v_fst_2838_);
v___f_2843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2843_, 0, v_fst_2838_);
lean_closure_set(v___f_2843_, 1, v_fvars_2723_);
lean_closure_set(v___f_2843_, 2, v_b_2729_);
lean_closure_set(v___f_2843_, 3, v___x_2840_);
lean_closure_set(v___f_2843_, 4, v_e_2724_);
lean_closure_set(v___f_2843_, 5, v_a_2755_);
lean_closure_set(v___f_2843_, 6, v_a_2760_);
lean_closure_set(v___f_2843_, 7, v___x_2841_);
lean_closure_set(v___f_2843_, 8, v___x_2842_);
v___x_2844_ = lean_unbox(v_fst_2838_);
lean_dec(v_fst_2838_);
if (v___x_2844_ == 0)
{
v___y_2818_ = v___f_2843_;
v___y_2819_ = v_snd_2839_;
v___y_2820_ = v___y_2831_;
v___y_2821_ = v___y_2835_;
v___y_2822_ = v___y_2834_;
v___y_2823_ = v___y_2830_;
v___y_2824_ = v___y_2833_;
v___y_2825_ = v___y_2829_;
v___y_2826_ = v___y_2832_;
goto v___jp_2817_;
}
else
{
if (v___y_2828_ == 0)
{
lean_del_object(v___x_2762_);
lean_del_object(v___x_2757_);
lean_dec_ref(v_b_2729_);
lean_dec_ref(v_e_2724_);
v___y_2801_ = v___f_2843_;
v___y_2802_ = v_snd_2839_;
v___y_2803_ = v___y_2835_;
v___y_2804_ = v___y_2831_;
v___y_2805_ = v___y_2834_;
v___y_2806_ = v___y_2833_;
v___y_2807_ = v___y_2830_;
v___y_2808_ = v___y_2829_;
v___y_2809_ = v___y_2832_;
goto v___jp_2800_;
}
else
{
v___y_2818_ = v___f_2843_;
v___y_2819_ = v_snd_2839_;
v___y_2820_ = v___y_2831_;
v___y_2821_ = v___y_2835_;
v___y_2822_ = v___y_2834_;
v___y_2823_ = v___y_2830_;
v___y_2824_ = v___y_2833_;
v___y_2825_ = v___y_2829_;
v___y_2826_ = v___y_2832_;
goto v___jp_2817_;
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_del_object(v___x_2762_);
lean_dec(v_a_2760_);
lean_del_object(v___x_2757_);
lean_dec(v_a_2755_);
lean_dec_ref(v_b_2729_);
lean_dec_ref(v_e_2724_);
lean_dec(v_fvars_2723_);
v_a_2845_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2836_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2836_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
v___jp_2853_:
{
if (v_merge_2815_ == 0)
{
v___y_2828_ = v___y_2854_;
v___y_2829_ = v_a_2731_;
v___y_2830_ = v_a_2732_;
v___y_2831_ = v_a_2733_;
v___y_2832_ = v_a_2734_;
v___y_2833_ = v_a_2735_;
v___y_2834_ = v_a_2736_;
v___y_2835_ = v_a_2737_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2855_; lean_object* v_valueMap_2856_; lean_object* v___x_2857_; 
v___x_2855_ = lean_st_ref_get(v_a_2733_);
v_valueMap_2856_ = lean_ctor_get(v___x_2855_, 2);
lean_inc_ref(v_valueMap_2856_);
lean_dec(v___x_2855_);
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2856_, v_a_2760_);
lean_dec_ref(v_valueMap_2856_);
if (lean_obj_tag(v___x_2857_) == 1)
{
lean_del_object(v___x_2762_);
lean_dec(v_a_2760_);
lean_del_object(v___x_2757_);
lean_dec(v_a_2755_);
lean_dec(v_n_2726_);
lean_dec_ref(v_e_2724_);
if (v_isLet_2725_ == 0)
{
lean_object* v_val_2858_; 
v_val_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_val_2858_);
lean_dec_ref(v___x_2857_);
v___y_2740_ = v_val_2858_;
v___y_2741_ = v_a_2731_;
v___y_2742_ = v_a_2732_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
goto v___jp_2739_;
}
else
{
if (v_lift_2816_ == 0)
{
lean_object* v_val_2859_; 
v_val_2859_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_val_2859_);
lean_dec_ref(v___x_2857_);
v___y_2740_ = v_val_2859_;
v___y_2741_ = v_a_2731_;
v___y_2742_ = v_a_2732_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
goto v___jp_2739_;
}
else
{
lean_object* v_val_2860_; lean_object* v___x_2861_; 
v_val_2860_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_val_2860_);
lean_dec_ref(v___x_2857_);
v___x_2861_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2860_, v_a_2733_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_dec_ref(v___x_2861_);
v___y_2740_ = v_val_2860_;
v___y_2741_ = v_a_2731_;
v___y_2742_ = v_a_2732_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
goto v___jp_2739_;
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_val_2860_);
lean_dec_ref(v_b_2729_);
lean_dec(v_fvars_2723_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2857_);
v___y_2828_ = v___y_2854_;
v___y_2829_ = v_a_2731_;
v___y_2830_ = v_a_2732_;
v___y_2831_ = v_a_2733_;
v___y_2832_ = v_a_2734_;
v___y_2833_ = v_a_2735_;
v___y_2834_ = v_a_2736_;
v___y_2835_ = v_a_2737_;
goto v___jp_2827_;
}
}
}
}
}
else
{
lean_del_object(v___x_2757_);
lean_dec(v_a_2755_);
lean_dec_ref(v_b_2729_);
lean_dec(v_n_2726_);
lean_dec_ref(v_e_2724_);
lean_dec(v_fvars_2723_);
return v___x_2759_;
}
}
}
else
{
lean_dec_ref(v_b_2729_);
lean_dec_ref(v_v_2728_);
lean_dec(v_n_2726_);
lean_dec_ref(v_e_2724_);
lean_dec(v_fvars_2723_);
return v___x_2754_;
}
v___jp_2739_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_inc(v___y_2740_);
v___x_2748_ = l_Lean_Expr_fvar___override(v___y_2740_);
v___x_2749_ = lean_expr_instantiate1(v_b_2729_, v___x_2748_);
lean_dec_ref(v___x_2748_);
lean_dec_ref(v_b_2729_);
v___x_2750_ = lean_box(v_topLevel_2730_);
v___x_2751_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2751_, 0, v_fvars_2723_);
lean_closure_set(v___x_2751_, 1, v___x_2749_);
lean_closure_set(v___x_2751_, 2, v___x_2750_);
lean_inc_ref(v___y_2744_);
v___x_2752_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2740_, v___x_2751_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
return v___x_2752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2874_, lean_object* v_struct_2875_, lean_object* v___y_2876_, lean_object* v_typeName_2877_, lean_object* v_idx_2878_, lean_object* v_e_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
uint8_t v___y_51423__boxed_2888_; lean_object* v_res_2889_; 
v___y_51423__boxed_2888_ = lean_unbox(v___y_2876_);
v_res_2889_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2874_, v_struct_2875_, v___y_51423__boxed_2888_, v_typeName_2877_, v_idx_2878_, v_e_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2889_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2893_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2894_ = lean_unsigned_to_nat(75u);
v___x_2895_ = lean_unsigned_to_nat(229u);
v___x_2896_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2897_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2898_ = l_mkPanicMessageWithDecl(v___x_2897_, v___x_2896_, v___x_2895_, v___x_2894_, v___x_2893_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2899_, lean_object* v_e_2900_, lean_object* v_fvars_2901_, uint8_t v___x_2902_, uint8_t v_topLevel_2903_, uint8_t v___y_2904_, lean_object* v_____r_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_k_2915_; 
switch(lean_obj_tag(v_e_2900_))
{
case 5:
{
lean_object* v___x_2918_; lean_object* v_dummy_2919_; lean_object* v_nargs_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2918_ = l_Lean_Expr_getAppFn(v_e_2900_);
v_dummy_2919_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2920_ = l_Lean_Expr_getAppNumArgs(v_e_2900_);
lean_inc(v_nargs_2920_);
v___x_2921_ = lean_mk_array(v_nargs_2920_, v_dummy_2919_);
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_sub(v_nargs_2920_, v___x_2922_);
lean_dec(v_nargs_2920_);
lean_inc_ref(v_e_2900_);
v___x_2924_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2900_, v___x_2921_, v___x_2923_);
v___x_2925_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2925_, 0, v_fvars_2901_);
lean_closure_set(v___x_2925_, 1, v___x_2918_);
lean_closure_set(v___x_2925_, 2, v___x_2924_);
v_k_2915_ = v___x_2925_;
goto v___jp_2914_;
}
case 6:
{
lean_object* v_binderName_2926_; lean_object* v_binderType_2927_; lean_object* v_body_2928_; uint8_t v_binderInfo_2929_; lean_object* v___x_2930_; lean_object* v___f_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_binderName_2926_ = lean_ctor_get(v_e_2900_, 0);
v_binderType_2927_ = lean_ctor_get(v_e_2900_, 1);
v_body_2928_ = lean_ctor_get(v_e_2900_, 2);
v_binderInfo_2929_ = lean_ctor_get_uint8(v_e_2900_, sizeof(void*)*3 + 8);
v___x_2930_ = lean_box(v_binderInfo_2929_);
lean_inc_ref(v_body_2928_);
lean_inc_ref(v_binderType_2927_);
lean_inc_ref(v_e_2900_);
lean_inc(v_binderName_2926_);
v___f_2931_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2931_, 0, v_binderName_2926_);
lean_closure_set(v___f_2931_, 1, v___x_2930_);
lean_closure_set(v___f_2931_, 2, v_e_2900_);
lean_closure_set(v___f_2931_, 3, v_binderType_2927_);
lean_closure_set(v___f_2931_, 4, v_body_2928_);
v___x_2932_ = lean_box(v_binderInfo_2929_);
lean_inc_ref(v_body_2928_);
lean_inc_ref(v_binderType_2927_);
lean_inc(v_binderName_2926_);
v___x_2933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2933_, 0, v_fvars_2901_);
lean_closure_set(v___x_2933_, 1, v_binderName_2926_);
lean_closure_set(v___x_2933_, 2, v_binderType_2927_);
lean_closure_set(v___x_2933_, 3, v_body_2928_);
lean_closure_set(v___x_2933_, 4, v___x_2932_);
lean_closure_set(v___x_2933_, 5, v___f_2931_);
v_k_2915_ = v___x_2933_;
goto v___jp_2914_;
}
case 7:
{
lean_object* v_binderName_2934_; lean_object* v_binderType_2935_; lean_object* v_body_2936_; uint8_t v_binderInfo_2937_; lean_object* v___x_2938_; lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_binderName_2934_ = lean_ctor_get(v_e_2900_, 0);
v_binderType_2935_ = lean_ctor_get(v_e_2900_, 1);
v_body_2936_ = lean_ctor_get(v_e_2900_, 2);
v_binderInfo_2937_ = lean_ctor_get_uint8(v_e_2900_, sizeof(void*)*3 + 8);
v___x_2938_ = lean_box(v_binderInfo_2937_);
lean_inc_ref(v_body_2936_);
lean_inc_ref(v_binderType_2935_);
lean_inc_ref(v_e_2900_);
lean_inc(v_binderName_2934_);
v___f_2939_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2939_, 0, v_binderName_2934_);
lean_closure_set(v___f_2939_, 1, v___x_2938_);
lean_closure_set(v___f_2939_, 2, v_e_2900_);
lean_closure_set(v___f_2939_, 3, v_binderType_2935_);
lean_closure_set(v___f_2939_, 4, v_body_2936_);
v___x_2940_ = lean_box(v_binderInfo_2937_);
lean_inc_ref(v_body_2936_);
lean_inc_ref(v_binderType_2935_);
lean_inc(v_binderName_2934_);
v___x_2941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2941_, 0, v_fvars_2901_);
lean_closure_set(v___x_2941_, 1, v_binderName_2934_);
lean_closure_set(v___x_2941_, 2, v_binderType_2935_);
lean_closure_set(v___x_2941_, 3, v_body_2936_);
lean_closure_set(v___x_2941_, 4, v___x_2940_);
lean_closure_set(v___x_2941_, 5, v___f_2939_);
v_k_2915_ = v___x_2941_;
goto v___jp_2914_;
}
case 8:
{
uint8_t v_nondep_2942_; 
v_nondep_2942_ = lean_ctor_get_uint8(v_e_2900_, sizeof(void*)*4 + 8);
if (v_nondep_2942_ == 0)
{
lean_object* v_declName_2943_; lean_object* v_type_2944_; lean_object* v_value_2945_; lean_object* v_body_2946_; lean_object* v___x_2947_; 
v_declName_2943_ = lean_ctor_get(v_e_2900_, 0);
lean_inc(v_declName_2943_);
v_type_2944_ = lean_ctor_get(v_e_2900_, 1);
lean_inc_ref(v_type_2944_);
v_value_2945_ = lean_ctor_get(v_e_2900_, 2);
lean_inc_ref(v_value_2945_);
v_body_2946_ = lean_ctor_get(v_e_2900_, 3);
lean_inc_ref(v_body_2946_);
v___x_2947_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2901_, v_e_2900_, v___x_2902_, v_declName_2943_, v_type_2944_, v_value_2945_, v_body_2946_, v_topLevel_2903_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
return v___x_2947_;
}
else
{
lean_object* v_declName_2948_; lean_object* v_type_2949_; lean_object* v_value_2950_; lean_object* v_body_2951_; lean_object* v___x_2952_; 
v_declName_2948_ = lean_ctor_get(v_e_2900_, 0);
lean_inc(v_declName_2948_);
v_type_2949_ = lean_ctor_get(v_e_2900_, 1);
lean_inc_ref(v_type_2949_);
v_value_2950_ = lean_ctor_get(v_e_2900_, 2);
lean_inc_ref(v_value_2950_);
v_body_2951_ = lean_ctor_get(v_e_2900_, 3);
lean_inc_ref(v_body_2951_);
v___x_2952_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2901_, v_e_2900_, v___y_2904_, v_declName_2948_, v_type_2949_, v_value_2950_, v_body_2951_, v_topLevel_2903_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
return v___x_2952_;
}
}
case 10:
{
lean_object* v_data_2953_; lean_object* v_expr_2954_; lean_object* v___x_2955_; 
v_data_2953_ = lean_ctor_get(v_e_2900_, 0);
v_expr_2954_ = lean_ctor_get(v_e_2900_, 1);
lean_inc_ref(v_expr_2954_);
v___x_2955_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2901_, v_expr_2954_, v_topLevel_2903_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2970_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
size_t v___x_2960_; size_t v___x_2961_; uint8_t v___x_2962_; 
v___x_2960_ = lean_ptr_addr(v_expr_2954_);
v___x_2961_ = lean_ptr_addr(v_a_2956_);
v___x_2962_ = lean_usize_dec_eq(v___x_2960_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
lean_inc(v_data_2953_);
lean_dec_ref(v_e_2900_);
v___x_2963_ = l_Lean_Expr_mdata___override(v_data_2953_, v_a_2956_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2963_);
v___x_2965_ = v___x_2958_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
else
{
lean_object* v___x_2968_; 
lean_dec(v_a_2956_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v_e_2900_);
v___x_2968_ = v___x_2958_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_e_2900_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_dec_ref(v_e_2900_);
return v___x_2955_;
}
}
case 11:
{
lean_object* v_typeName_2971_; lean_object* v_idx_2972_; lean_object* v_struct_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; 
v_typeName_2971_ = lean_ctor_get(v_e_2900_, 0);
v_idx_2972_ = lean_ctor_get(v_e_2900_, 1);
v_struct_2973_ = lean_ctor_get(v_e_2900_, 2);
v___x_2974_ = lean_box(v___y_2904_);
lean_inc_ref(v_e_2900_);
lean_inc(v_idx_2972_);
lean_inc(v_typeName_2971_);
lean_inc_ref(v_struct_2973_);
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2975_, 0, v_fvars_2901_);
lean_closure_set(v___f_2975_, 1, v_struct_2973_);
lean_closure_set(v___f_2975_, 2, v___x_2974_);
lean_closure_set(v___f_2975_, 3, v_typeName_2971_);
lean_closure_set(v___f_2975_, 4, v_idx_2972_);
lean_closure_set(v___f_2975_, 5, v_e_2900_);
v_k_2915_ = v___f_2975_;
goto v___jp_2914_;
}
default: 
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec(v_fvars_2901_);
lean_dec_ref(v_e_2900_);
v___x_2976_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2977_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2976_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
return v___x_2977_;
}
}
v___jp_2914_:
{
if (v_descend_2899_ == 0)
{
lean_object* v___x_2916_; 
lean_dec_ref(v_k_2915_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_e_2900_);
return v___x_2916_;
}
else
{
lean_object* v___x_2917_; 
lean_dec_ref(v_e_2900_);
lean_inc(v___y_2912_);
lean_inc_ref(v___y_2911_);
lean_inc(v___y_2910_);
lean_inc_ref(v___y_2909_);
lean_inc(v___y_2908_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
v___x_2917_ = lean_apply_8(v_k_2915_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, lean_box(0));
return v___x_2917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2978_, lean_object* v_e_2979_, lean_object* v_fvars_2980_, lean_object* v___x_2981_, lean_object* v_topLevel_2982_, lean_object* v___y_2983_, lean_object* v_____r_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
uint8_t v_descend_boxed_2993_; uint8_t v___x_51576__boxed_2994_; uint8_t v_topLevel_boxed_2995_; uint8_t v___y_51577__boxed_2996_; lean_object* v_res_2997_; 
v_descend_boxed_2993_ = lean_unbox(v_descend_2978_);
v___x_51576__boxed_2994_ = lean_unbox(v___x_2981_);
v_topLevel_boxed_2995_ = lean_unbox(v_topLevel_2982_);
v___y_51577__boxed_2996_ = lean_unbox(v___y_2983_);
v_res_2997_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2993_, v_e_2979_, v_fvars_2980_, v___x_51576__boxed_2994_, v_topLevel_boxed_2995_, v___y_51577__boxed_2996_, v_____r_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_2998_, lean_object* v_e_2999_, uint8_t v_topLevel_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v___y_3010_; lean_object* v_a_3011_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3021_; lean_object* v___y_3022_; uint8_t v___x_3025_; 
v___x_3025_ = l_Lean_Expr_isAtomic(v_e_2999_);
if (v___x_3025_ == 0)
{
uint8_t v_proofs_3026_; uint8_t v_types_3027_; uint8_t v_descend_3028_; lean_object* v___y_3030_; lean_object* v___y_3031_; uint8_t v___y_3048_; 
v_proofs_3026_ = lean_ctor_get_uint8(v_a_3001_, 0);
v_types_3027_ = lean_ctor_get_uint8(v_a_3001_, 1);
v_descend_3028_ = lean_ctor_get_uint8(v_a_3001_, 3);
if (v_descend_3028_ == 0)
{
goto v___jp_3071_;
}
else
{
if (v___x_3025_ == 0)
{
v___y_3048_ = v___x_3025_;
goto v___jp_3047_;
}
else
{
goto v___jp_3071_;
}
}
v___jp_3029_:
{
if (v_proofs_3026_ == 0)
{
lean_object* v___x_3032_; 
lean_inc_ref(v_e_2999_);
v___x_3032_ = l_Lean_Meta_isProof(v_e_2999_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; uint8_t v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref(v___x_3032_);
v___x_3034_ = lean_unbox(v_a_3033_);
lean_dec(v_a_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref(v_e_2999_);
v___x_3035_ = lean_box(0);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
lean_inc_ref(v_a_3004_);
lean_inc(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
v___x_3036_ = lean_apply_9(v___y_3030_, v___x_3035_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, lean_box(0));
v___y_3017_ = v___y_3031_;
v___y_3018_ = v___x_3036_;
goto v___jp_3016_;
}
else
{
lean_dec_ref(v___y_3030_);
v___y_3010_ = v___y_3031_;
v_a_3011_ = v_e_2999_;
goto v___jp_3009_;
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v_e_2999_);
v_a_3037_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3032_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3032_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v_e_2999_);
v___x_3045_ = lean_box(0);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
lean_inc_ref(v_a_3004_);
lean_inc(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
v___x_3046_ = lean_apply_9(v___y_3030_, v___x_3045_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, lean_box(0));
v___y_3017_ = v___y_3031_;
v___y_3018_ = v___x_3046_;
goto v___jp_3016_;
}
}
v___jp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = lean_st_ref_get(v_a_3002_);
v___x_3050_ = lean_box(v_topLevel_3000_);
lean_inc_ref(v_e_2999_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v_e_2999_);
v___x_3052_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3049_, v___x_3051_);
lean_dec(v___x_3049_);
if (lean_obj_tag(v___x_3052_) == 0)
{
uint8_t v___x_3053_; 
v___x_3053_ = l_Lean_Meta_ExtractLets_containsLet(v_e_2999_);
if (v___x_3053_ == 0)
{
lean_dec(v_fvars_2998_);
v___y_3010_ = v___x_3051_;
v_a_3011_ = v_e_2999_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v___f_3060_; 
v___x_3054_ = lean_box(v_descend_3028_);
v___x_3055_ = lean_box(v___x_3053_);
v___x_3056_ = lean_box(v_topLevel_3000_);
v___x_3057_ = lean_box(v___y_3048_);
lean_inc_ref(v_e_2999_);
v___f_3058_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3058_, 0, v___x_3054_);
lean_closure_set(v___f_3058_, 1, v_e_2999_);
lean_closure_set(v___f_3058_, 2, v_fvars_2998_);
lean_closure_set(v___f_3058_, 3, v___x_3055_);
lean_closure_set(v___f_3058_, 4, v___x_3056_);
lean_closure_set(v___f_3058_, 5, v___x_3057_);
v___x_3059_ = lean_box(v_types_3027_);
lean_inc_ref(v___f_3058_);
lean_inc_ref(v_e_2999_);
v___f_3060_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3060_, 0, v___x_3059_);
lean_closure_set(v___f_3060_, 1, v_e_2999_);
lean_closure_set(v___f_3060_, 2, v___f_3058_);
if (v_topLevel_3000_ == 0)
{
lean_dec_ref(v___f_3058_);
v___y_3030_ = v___f_3060_;
v___y_3031_ = v___x_3051_;
goto v___jp_3029_;
}
else
{
uint8_t v___x_3061_; 
v___x_3061_ = l_Lean_Expr_isLet(v_e_2999_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_Expr_isMData(v_e_2999_);
if (v___x_3062_ == 0)
{
lean_dec_ref(v___f_3058_);
v___y_3030_ = v___f_3060_;
v___y_3031_ = v___x_3051_;
goto v___jp_3029_;
}
else
{
lean_dec_ref(v___f_3060_);
lean_dec_ref(v_e_2999_);
v___y_3021_ = v___f_3058_;
v___y_3022_ = v___x_3051_;
goto v___jp_3020_;
}
}
else
{
lean_dec_ref(v___f_3060_);
lean_dec_ref(v_e_2999_);
v___y_3021_ = v___f_3058_;
v___y_3022_ = v___x_3051_;
goto v___jp_3020_;
}
}
}
}
else
{
lean_object* v_val_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v___x_3051_);
lean_dec_ref(v_e_2999_);
lean_dec(v_fvars_2998_);
v_val_3063_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3052_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_val_3063_);
lean_dec(v___x_3052_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set_tag(v___x_3065_, 0);
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_val_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
v___jp_3071_:
{
if (v_topLevel_3000_ == 0)
{
lean_object* v___x_3072_; 
lean_dec(v_fvars_2998_);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_e_2999_);
return v___x_3072_;
}
else
{
if (v___x_3025_ == 0)
{
v___y_3048_ = v___x_3025_;
goto v___jp_3047_;
}
else
{
lean_object* v___x_3073_; 
lean_dec(v_fvars_2998_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v_e_2999_);
return v___x_3073_;
}
}
}
}
else
{
lean_object* v___x_3074_; 
lean_dec(v_fvars_2998_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_e_2999_);
return v___x_3074_;
}
v___jp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3012_ = lean_st_ref_take(v_a_3002_);
lean_inc_ref(v_a_3011_);
v___x_3013_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3012_, v___y_3010_, v_a_3011_);
v___x_3014_ = lean_st_ref_set(v_a_3002_, v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_a_3011_);
return v___x_3015_;
}
v___jp_3016_:
{
if (lean_obj_tag(v___y_3018_) == 0)
{
lean_object* v_a_3019_; 
v_a_3019_ = lean_ctor_get(v___y_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref(v___y_3018_);
v___y_3010_ = v___y_3017_;
v_a_3011_ = v_a_3019_;
goto v___jp_3009_;
}
else
{
lean_dec_ref(v___y_3017_);
return v___y_3018_;
}
}
v___jp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_box(0);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
lean_inc_ref(v_a_3004_);
lean_inc(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
v___x_3024_ = lean_apply_9(v___y_3021_, v___x_3023_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, lean_box(0));
v___y_3017_ = v___y_3022_;
v___y_3018_ = v___x_3024_;
goto v___jp_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3075_, lean_object* v_struct_3076_, uint8_t v___y_3077_, lean_object* v_typeName_3078_, lean_object* v_idx_3079_, lean_object* v_e_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3089_; 
lean_inc_ref(v_struct_3076_);
v___x_3089_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3075_, v_struct_3076_, v___y_3077_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3104_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3104_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3104_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
size_t v___x_3094_; size_t v___x_3095_; uint8_t v___x_3096_; 
v___x_3094_ = lean_ptr_addr(v_struct_3076_);
lean_dec_ref(v_struct_3076_);
v___x_3095_ = lean_ptr_addr(v_a_3090_);
v___x_3096_ = lean_usize_dec_eq(v___x_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
lean_dec_ref(v_e_3080_);
v___x_3097_ = l_Lean_Expr_proj___override(v_typeName_3078_, v_idx_3079_, v_a_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3097_);
v___x_3099_ = v___x_3092_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
else
{
lean_object* v___x_3102_; 
lean_dec(v_a_3090_);
lean_dec(v_idx_3079_);
lean_dec(v_typeName_3078_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v_e_3080_);
v___x_3102_ = v___x_3092_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_e_3080_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_dec_ref(v_e_3080_);
lean_dec(v_idx_3079_);
lean_dec(v_typeName_3078_);
lean_dec_ref(v_struct_3076_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3105_, lean_object* v_sz_3106_, lean_object* v_i_3107_, lean_object* v_bs_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
size_t v_sz_boxed_3117_; size_t v_i_boxed_3118_; lean_object* v_res_3119_; 
v_sz_boxed_3117_ = lean_unbox_usize(v_sz_3106_);
lean_dec(v_sz_3106_);
v_i_boxed_3118_ = lean_unbox_usize(v_i_3107_);
lean_dec(v_i_3107_);
v_res_3119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3105_, v_sz_boxed_3117_, v_i_boxed_3118_, v_bs_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3120_, lean_object* v_fst_3121_, lean_object* v_fvars_3122_, lean_object* v_a_3123_, lean_object* v_b_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3120_, v_fst_3121_, v_fvars_3122_, v_a_3123_, v_b_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec_ref(v_fst_3121_);
lean_dec(v_upperBound_3120_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3134_, lean_object* v_e_3135_, lean_object* v_isLet_3136_, lean_object* v_n_3137_, lean_object* v_t_3138_, lean_object* v_v_3139_, lean_object* v_b_3140_, lean_object* v_topLevel_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
uint8_t v_isLet_boxed_3150_; uint8_t v_topLevel_boxed_3151_; lean_object* v_res_3152_; 
v_isLet_boxed_3150_ = lean_unbox(v_isLet_3136_);
v_topLevel_boxed_3151_ = lean_unbox(v_topLevel_3141_);
v_res_3152_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3134_, v_e_3135_, v_isLet_boxed_3150_, v_n_3137_, v_t_3138_, v_v_3139_, v_b_3140_, v_topLevel_boxed_3151_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3153_, lean_object* v_name_3154_, lean_object* v_type_3155_, lean_object* v_val_3156_, lean_object* v_k_3157_, uint8_t v_nondep_3158_, uint8_t v_kind_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3154_, v_type_3155_, v_val_3156_, v_k_3157_, v_nondep_3158_, v_kind_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3169_, lean_object* v_name_3170_, lean_object* v_type_3171_, lean_object* v_val_3172_, lean_object* v_k_3173_, lean_object* v_nondep_3174_, lean_object* v_kind_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
uint8_t v_nondep_boxed_3184_; uint8_t v_kind_boxed_3185_; lean_object* v_res_3186_; 
v_nondep_boxed_3184_ = lean_unbox(v_nondep_3174_);
v_kind_boxed_3185_ = lean_unbox(v_kind_3175_);
v_res_3186_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3169_, v_name_3170_, v_type_3171_, v_val_3172_, v_k_3173_, v_nondep_boxed_3184_, v_kind_boxed_3185_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3187_, lean_object* v_m_3188_, lean_object* v_a_3189_, lean_object* v_b_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3188_, v_a_3189_, v_b_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3192_, lean_object* v_m_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3193_, v_a_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3196_, lean_object* v_m_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3196_, v_m_3197_, v_a_3198_);
lean_dec_ref(v_a_3198_);
lean_dec_ref(v_m_3197_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3200_, lean_object* v_fst_3201_, lean_object* v_fvars_3202_, lean_object* v_inst_3203_, lean_object* v_R_3204_, lean_object* v_a_3205_, lean_object* v_b_3206_, lean_object* v_c_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3200_, v_fst_3201_, v_fvars_3202_, v_a_3205_, v_b_3206_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3217_, lean_object* v_fst_3218_, lean_object* v_fvars_3219_, lean_object* v_inst_3220_, lean_object* v_R_3221_, lean_object* v_a_3222_, lean_object* v_b_3223_, lean_object* v_c_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3217_, v_fst_3218_, v_fvars_3219_, v_inst_3220_, v_R_3221_, v_a_3222_, v_b_3223_, v_c_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v_fst_3218_);
lean_dec(v_upperBound_3217_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3234_, lean_object* v_m_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3235_, v_a_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3238_, lean_object* v_m_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3238_, v_m_3239_, v_a_3240_);
lean_dec_ref(v_a_3240_);
lean_dec_ref(v_m_3239_);
return v_res_3241_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3242_, lean_object* v_a_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3243_, v_x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3246_, lean_object* v_a_3247_, lean_object* v_x_3248_){
_start:
{
uint8_t v_res_3249_; lean_object* v_r_3250_; 
v_res_3249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3246_, v_a_3247_, v_x_3248_);
lean_dec(v_x_3248_);
lean_dec_ref(v_a_3247_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3251_, lean_object* v_data_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3254_, lean_object* v_a_3255_, lean_object* v_b_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3255_, v_b_3256_, v_x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3259_, lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3263_, lean_object* v_a_3264_, lean_object* v_x_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3263_, v_a_3264_, v_x_3265_);
lean_dec(v_x_3265_);
lean_dec_ref(v_a_3264_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3267_, lean_object* v_a_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3268_, v_x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3271_, lean_object* v_a_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3271_, v_a_3272_, v_x_3273_);
lean_dec(v_x_3273_);
lean_dec_ref(v_a_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3275_, lean_object* v_i_3276_, lean_object* v_source_3277_, lean_object* v_target_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3276_, v_source_3277_, v_target_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3281_, v_x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3293_; lean_object* v_a_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; 
v___x_3293_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3284_, v_a_3289_);
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref(v___x_3293_);
v___x_3295_ = lean_box(0);
v___x_3296_ = 1;
v___x_3297_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3295_, v_a_3294_, v___x_3296_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3308_, size_t v_i_3309_, lean_object* v_bs_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
uint8_t v___x_3319_; 
v___x_3319_ = lean_usize_dec_lt(v_i_3309_, v_sz_3308_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_bs_3310_);
return v___x_3320_;
}
else
{
lean_object* v_v_3321_; lean_object* v___x_3322_; 
v_v_3321_ = lean_array_uget_borrowed(v_bs_3310_, v_i_3309_);
lean_inc(v_v_3321_);
v___x_3322_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3321_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; lean_object* v_bs_x27_3325_; size_t v___x_3326_; size_t v___x_3327_; lean_object* v___x_3328_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref(v___x_3322_);
v___x_3324_ = lean_unsigned_to_nat(0u);
v_bs_x27_3325_ = lean_array_uset(v_bs_3310_, v_i_3309_, v___x_3324_);
v___x_3326_ = ((size_t)1ULL);
v___x_3327_ = lean_usize_add(v_i_3309_, v___x_3326_);
v___x_3328_ = lean_array_uset(v_bs_x27_3325_, v_i_3309_, v_a_3323_);
v_i_3309_ = v___x_3327_;
v_bs_3310_ = v___x_3328_;
goto _start;
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v_bs_3310_);
v_a_3330_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3322_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3322_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3338_, lean_object* v_i_3339_, lean_object* v_bs_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
size_t v_sz_boxed_3349_; size_t v_i_boxed_3350_; lean_object* v_res_3351_; 
v_sz_boxed_3349_ = lean_unbox_usize(v_sz_3338_);
lean_dec(v_sz_3338_);
v_i_boxed_3350_ = lean_unbox_usize(v_i_3339_);
lean_dec(v_i_3339_);
v_res_3351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3349_, v_i_boxed_3350_, v_bs_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; uint8_t v_merge_3372_; 
v_merge_3372_ = lean_ctor_get_uint8(v_a_3353_, 6);
if (v_merge_3372_ == 0)
{
v___y_3362_ = v_a_3353_;
v___y_3363_ = v_a_3354_;
v___y_3364_ = v_a_3355_;
v___y_3365_ = v_a_3356_;
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
goto v___jp_3361_;
}
else
{
uint8_t v_useContext_3373_; 
v_useContext_3373_ = lean_ctor_get_uint8(v_a_3353_, 7);
if (v_useContext_3373_ == 0)
{
v___y_3362_ = v_a_3353_;
v___y_3363_ = v_a_3354_;
v___y_3364_ = v_a_3355_;
v___y_3365_ = v_a_3356_;
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
goto v___jp_3361_;
}
else
{
lean_object* v___x_3374_; 
lean_inc_ref(v_a_3356_);
v___x_3374_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_dec_ref(v___x_3374_);
v___y_3362_ = v_a_3353_;
v___y_3363_ = v_a_3354_;
v___y_3364_ = v_a_3355_;
v___y_3365_ = v_a_3356_;
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
goto v___jp_3361_;
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v_es_3352_);
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
v___jp_3361_:
{
size_t v_sz_3369_; size_t v___x_3370_; lean_object* v___x_3371_; 
v_sz_3369_ = lean_array_size(v_es_3352_);
v___x_3370_ = ((size_t)0ULL);
v___x_3371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3369_, v___x_3370_, v_es_3352_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Meta_ExtractLets_extract(v_es_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3393_, lean_object* v_x_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3393_, v_x_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_a_3409_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3400_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3400_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3417_, lean_object* v_x_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3417_, v_x_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3425_, lean_object* v_decls_3426_, lean_object* v_x_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3426_, v_x_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3434_, lean_object* v_decls_3435_, lean_object* v_x_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3434_, v_decls_3435_, v_x_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3443_, size_t v_i_3444_, lean_object* v_bs_3445_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3444_, v_sz_3443_);
if (v___x_3446_ == 0)
{
return v_bs_3445_;
}
else
{
lean_object* v_v_3447_; lean_object* v___x_3448_; lean_object* v_bs_x27_3449_; lean_object* v___x_3450_; size_t v___x_3451_; size_t v___x_3452_; lean_object* v___x_3453_; 
v_v_3447_ = lean_array_uget(v_bs_3445_, v_i_3444_);
v___x_3448_ = lean_unsigned_to_nat(0u);
v_bs_x27_3449_ = lean_array_uset(v_bs_3445_, v_i_3444_, v___x_3448_);
v___x_3450_ = l_Lean_LocalDecl_fvarId(v_v_3447_);
lean_dec(v_v_3447_);
v___x_3451_ = ((size_t)1ULL);
v___x_3452_ = lean_usize_add(v_i_3444_, v___x_3451_);
v___x_3453_ = lean_array_uset(v_bs_x27_3449_, v_i_3444_, v___x_3450_);
v_i_3444_ = v___x_3452_;
v_bs_3445_ = v___x_3453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3455_, lean_object* v_i_3456_, lean_object* v_bs_3457_){
_start:
{
size_t v_sz_boxed_3458_; size_t v_i_boxed_3459_; lean_object* v_res_3460_; 
v_sz_boxed_3458_ = lean_unbox_usize(v_sz_3455_);
lean_dec(v_sz_3455_);
v_i_boxed_3459_ = lean_unbox_usize(v_i_3456_);
lean_dec(v_i_3456_);
v_res_3460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3458_, v_i_boxed_3459_, v_bs_3457_);
return v_res_3460_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_box(0);
v___x_3462_ = lean_unsigned_to_nat(16u);
v___x_3463_ = lean_mk_array(v___x_3462_, v___x_3461_);
return v___x_3463_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3465_ = lean_unsigned_to_nat(0u);
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_3464_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3467_, lean_object* v_givenNames_3468_, lean_object* v_k_3469_, lean_object* v_config_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3477_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_3478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3478_, 0, v_givenNames_3468_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
lean_ctor_set(v___x_3478_, 2, v___x_3476_);
v___x_3479_ = lean_st_mk_ref(v___x_3478_);
v___x_3480_ = lean_st_mk_ref(v___x_3476_);
v___x_3481_ = l_Lean_Meta_ExtractLets_extract(v_es_3467_, v_config_3470_, v___x_3480_, v___x_3479_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v_givenNames_3485_; lean_object* v_decls_3486_; size_t v_sz_3487_; size_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; size_t v_sz_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = lean_st_ref_get(v___x_3480_);
lean_dec(v___x_3480_);
lean_dec(v___x_3483_);
v___x_3484_ = lean_st_ref_get(v___x_3479_);
lean_dec(v___x_3479_);
v_givenNames_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_givenNames_3485_);
v_decls_3486_ = lean_ctor_get(v___x_3484_, 1);
lean_inc_ref(v_decls_3486_);
lean_dec(v___x_3484_);
v_sz_3487_ = lean_array_size(v_decls_3486_);
v___x_3488_ = ((size_t)0ULL);
v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_3487_, v___x_3488_, v_decls_3486_);
lean_inc_ref(v___x_3489_);
v___x_3490_ = lean_array_to_list(v___x_3489_);
v_sz_3491_ = lean_array_size(v___x_3489_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3491_, v___x_3488_, v___x_3489_);
v___x_3493_ = lean_apply_3(v_k_3469_, v___x_3492_, v_a_3482_, v_givenNames_3485_);
v___x_3494_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3490_, v___x_3493_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
return v___x_3494_;
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v___x_3480_);
lean_dec(v___x_3479_);
lean_dec_ref(v_k_3469_);
v_a_3495_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3481_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3481_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3503_, lean_object* v_givenNames_3504_, lean_object* v_k_3505_, lean_object* v_config_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3503_, v_givenNames_3504_, v_k_3505_, v_config_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
lean_dec_ref(v_config_3506_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3513_, lean_object* v_es_3514_, lean_object* v_givenNames_3515_, lean_object* v_k_3516_, lean_object* v_config_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3514_, v_givenNames_3515_, v_k_3516_, v_config_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3524_, lean_object* v_es_3525_, lean_object* v_givenNames_3526_, lean_object* v_k_3527_, lean_object* v_config_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3524_, v_es_3525_, v_givenNames_3526_, v_k_3527_, v_config_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec_ref(v_config_3528_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3535_, lean_object* v_runInBase_3536_, lean_object* v_b_3537_, lean_object* v_c_3538_, lean_object* v_d_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = lean_apply_3(v_k_3535_, v_b_3537_, v_c_3538_, v_d_3539_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
v___x_3546_ = lean_apply_7(v_runInBase_3536_, lean_box(0), v___x_3545_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, lean_box(0));
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3547_, lean_object* v_runInBase_3548_, lean_object* v_b_3549_, lean_object* v_c_3550_, lean_object* v_d_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3547_, v_runInBase_3548_, v_b_3549_, v_c_3550_, v_d_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3558_, lean_object* v_es_3559_, lean_object* v_givenNames_3560_, lean_object* v_config_3561_, lean_object* v_runInBase_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___f_3568_; lean_object* v___x_3569_; 
v___f_3568_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3568_, 0, v_k_3558_);
lean_closure_set(v___f_3568_, 1, v_runInBase_3562_);
v___x_3569_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3559_, v_givenNames_3560_, v___f_3568_, v_config_3561_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3570_, lean_object* v_es_3571_, lean_object* v_givenNames_3572_, lean_object* v_config_3573_, lean_object* v_runInBase_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3570_, v_es_3571_, v_givenNames_3572_, v_config_3573_, v_runInBase_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec_ref(v_config_3573_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3581_, lean_object* v_inst_3582_, lean_object* v_es_3583_, lean_object* v_givenNames_3584_, lean_object* v_k_3585_, lean_object* v_config_3586_){
_start:
{
lean_object* v_toBind_3587_; lean_object* v_liftWith_3588_; lean_object* v_restoreM_3589_; lean_object* v___f_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v_toBind_3587_ = lean_ctor_get(v_inst_3581_, 1);
lean_inc(v_toBind_3587_);
lean_dec_ref(v_inst_3581_);
v_liftWith_3588_ = lean_ctor_get(v_inst_3582_, 0);
lean_inc(v_liftWith_3588_);
v_restoreM_3589_ = lean_ctor_get(v_inst_3582_, 1);
lean_inc(v_restoreM_3589_);
lean_dec_ref(v_inst_3582_);
v___f_3590_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3590_, 0, v_k_3585_);
lean_closure_set(v___f_3590_, 1, v_es_3583_);
lean_closure_set(v___f_3590_, 2, v_givenNames_3584_);
lean_closure_set(v___f_3590_, 3, v_config_3586_);
v___x_3591_ = lean_apply_2(v_liftWith_3588_, lean_box(0), v___f_3590_);
v___x_3592_ = lean_apply_1(v_restoreM_3589_, lean_box(0));
v___x_3593_ = lean_apply_4(v_toBind_3587_, lean_box(0), lean_box(0), v___x_3591_, v___x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3594_, lean_object* v_00_u03b1_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_es_3598_, lean_object* v_givenNames_3599_, lean_object* v_k_3600_, lean_object* v_config_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Meta_extractLets___redArg(v_inst_3596_, v_inst_3597_, v_es_3598_, v_givenNames_3599_, v_k_3600_, v_config_3601_);
return v___x_3602_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3604_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_3605_ = lean_box(0);
v___x_3606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___x_3604_);
lean_ctor_set(v___x_3606_, 2, v___x_3603_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3607_, lean_object* v_config_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v_proofs_3619_; uint8_t v_types_3620_; uint8_t v_implicits_3621_; uint8_t v_descend_3622_; uint8_t v_underBinder_3623_; uint8_t v_usedOnly_3624_; uint8_t v_merge_3625_; uint8_t v_useContext_3626_; uint8_t v_preserveBinderNames_3627_; uint8_t v_lift_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3662_; 
v___x_3614_ = lean_unsigned_to_nat(0u);
v___x_3615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3616_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3617_ = lean_st_mk_ref(v___x_3616_);
v___x_3618_ = lean_st_mk_ref(v___x_3615_);
v_proofs_3619_ = lean_ctor_get_uint8(v_config_3608_, 0);
v_types_3620_ = lean_ctor_get_uint8(v_config_3608_, 1);
v_implicits_3621_ = lean_ctor_get_uint8(v_config_3608_, 2);
v_descend_3622_ = lean_ctor_get_uint8(v_config_3608_, 3);
v_underBinder_3623_ = lean_ctor_get_uint8(v_config_3608_, 4);
v_usedOnly_3624_ = lean_ctor_get_uint8(v_config_3608_, 5);
v_merge_3625_ = lean_ctor_get_uint8(v_config_3608_, 6);
v_useContext_3626_ = lean_ctor_get_uint8(v_config_3608_, 7);
v_preserveBinderNames_3627_ = lean_ctor_get_uint8(v_config_3608_, 9);
v_lift_3628_ = lean_ctor_get_uint8(v_config_3608_, 10);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_config_3608_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3630_ = v_config_3608_;
v_isShared_3631_ = v_isSharedCheck_3662_;
goto v_resetjp_3629_;
}
else
{
lean_dec(v_config_3608_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3662_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; lean_object* v___x_3637_; 
v___x_3632_ = lean_unsigned_to_nat(1u);
v___x_3633_ = lean_mk_empty_array_with_capacity(v___x_3632_);
v___x_3634_ = lean_array_push(v___x_3633_, v_e_3607_);
v___x_3635_ = 1;
if (v_isShared_3631_ == 0)
{
v___x_3637_ = v___x_3630_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 0, v_proofs_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 1, v_types_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 2, v_implicits_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 3, v_descend_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 4, v_underBinder_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 5, v_usedOnly_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 6, v_merge_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 7, v_useContext_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 9, v_preserveBinderNames_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, 10, v_lift_3628_);
v___x_3637_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3638_; 
lean_ctor_set_uint8(v___x_3637_, 8, v___x_3635_);
v___x_3638_ = l_Lean_Meta_ExtractLets_extract(v___x_3634_, v___x_3637_, v___x_3618_, v___x_3617_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
lean_dec_ref(v___x_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3652_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3652_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3652_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_decls_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3643_ = lean_st_ref_get(v___x_3618_);
lean_dec(v___x_3618_);
lean_dec(v___x_3643_);
v___x_3644_ = lean_st_ref_get(v___x_3617_);
lean_dec(v___x_3617_);
v_decls_3645_ = lean_ctor_get(v___x_3644_, 1);
lean_inc_ref(v_decls_3645_);
lean_dec(v___x_3644_);
v___x_3646_ = l_Lean_instInhabitedExpr;
v___x_3647_ = lean_array_get(v___x_3646_, v_a_3639_, v___x_3614_);
lean_dec(v_a_3639_);
v___x_3648_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3645_, v___x_3647_);
lean_dec_ref(v_decls_3645_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3648_);
v___x_3650_ = v___x_3641_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v___x_3618_);
lean_dec(v___x_3617_);
v_a_3653_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3638_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3638_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3663_, lean_object* v_config_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_Meta_liftLets(v_e_3663_, v_config_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
lean_dec(v_a_3666_);
lean_dec_ref(v_a_3665_);
return v_res_3670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3673_ = l_Lean_stringToMessageData(v___x_3672_);
return v___x_3673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3676_, lean_object* v_mvarId_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3684_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3676_, v_mvarId_3677_, v___x_3683_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3685_, lean_object* v_mvarId_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3685_, v_mvarId_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3693_, lean_object* v_tactic_3694_, lean_object* v_mvarId_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3694_, v_mvarId_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3702_, lean_object* v_tactic_3703_, lean_object* v_mvarId_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3702_, v_tactic_3703_, v_mvarId_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3711_, lean_object* v_b_3712_, lean_object* v_c_3713_, lean_object* v_d_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___x_3720_; 
lean_inc(v___y_3718_);
lean_inc_ref(v___y_3717_);
lean_inc(v___y_3716_);
lean_inc_ref(v___y_3715_);
v___x_3720_ = lean_apply_8(v_k_3711_, v_b_3712_, v_c_3713_, v_d_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, lean_box(0));
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3721_, lean_object* v_b_3722_, lean_object* v_c_3723_, lean_object* v_d_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3721_, v_b_3722_, v_c_3723_, v_d_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3731_, lean_object* v_givenNames_3732_, lean_object* v_k_3733_, lean_object* v_config_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v___f_3740_; lean_object* v___x_3741_; 
v___f_3740_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3740_, 0, v_k_3733_);
v___x_3741_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3731_, v_givenNames_3732_, v___f_3740_, v_config_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
v_a_3750_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3741_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3741_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3758_, lean_object* v_givenNames_3759_, lean_object* v_k_3760_, lean_object* v_config_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3758_, v_givenNames_3759_, v_k_3760_, v_config_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec_ref(v_config_3761_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3768_, lean_object* v_es_3769_, lean_object* v_givenNames_3770_, lean_object* v_k_3771_, lean_object* v_config_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3769_, v_givenNames_3770_, v_k_3771_, v_config_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3779_, lean_object* v_es_3780_, lean_object* v_givenNames_3781_, lean_object* v_k_3782_, lean_object* v_config_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3779_, v_es_3780_, v_givenNames_3781_, v_k_3782_, v_config_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec_ref(v_config_3783_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3790_, lean_object* v_x_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3790_, v_x_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_a_3806_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3797_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3797_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3814_, lean_object* v_x_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3814_, v_x_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3822_, lean_object* v_mvarId_3823_, lean_object* v_x_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3823_, v_x_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_mvarId_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3831_, v_mvarId_3832_, v_x_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3840_, lean_object* v_x_3841_, lean_object* v_x_3842_, lean_object* v_x_3843_){
_start:
{
lean_object* v_ks_3844_; lean_object* v_vs_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3869_; 
v_ks_3844_ = lean_ctor_get(v_x_3840_, 0);
v_vs_3845_ = lean_ctor_get(v_x_3840_, 1);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_x_3840_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3847_ = v_x_3840_;
v_isShared_3848_ = v_isSharedCheck_3869_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_vs_3845_);
lean_inc(v_ks_3844_);
lean_dec(v_x_3840_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3869_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3849_; uint8_t v___x_3850_; 
v___x_3849_ = lean_array_get_size(v_ks_3844_);
v___x_3850_ = lean_nat_dec_lt(v_x_3841_, v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
lean_dec(v_x_3841_);
v___x_3851_ = lean_array_push(v_ks_3844_, v_x_3842_);
v___x_3852_ = lean_array_push(v_vs_3845_, v_x_3843_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 1, v___x_3852_);
lean_ctor_set(v___x_3847_, 0, v___x_3851_);
v___x_3854_ = v___x_3847_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
else
{
lean_object* v_k_x27_3856_; uint8_t v___x_3857_; 
v_k_x27_3856_ = lean_array_fget_borrowed(v_ks_3844_, v_x_3841_);
v___x_3857_ = l_Lean_instBEqMVarId_beq(v_x_3842_, v_k_x27_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3859_; 
if (v_isShared_3848_ == 0)
{
v___x_3859_ = v___x_3847_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_ks_3844_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_vs_3845_);
v___x_3859_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_unsigned_to_nat(1u);
v___x_3861_ = lean_nat_add(v_x_3841_, v___x_3860_);
lean_dec(v_x_3841_);
v_x_3840_ = v___x_3859_;
v_x_3841_ = v___x_3861_;
goto _start;
}
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3864_ = lean_array_fset(v_ks_3844_, v_x_3841_, v_x_3842_);
v___x_3865_ = lean_array_fset(v_vs_3845_, v_x_3841_, v_x_3843_);
lean_dec(v_x_3841_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 1, v___x_3865_);
lean_ctor_set(v___x_3847_, 0, v___x_3864_);
v___x_3867_ = v___x_3847_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3870_, lean_object* v_k_3871_, lean_object* v_v_3872_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_unsigned_to_nat(0u);
v___x_3874_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3870_, v___x_3873_, v_k_3871_, v_v_3872_);
return v___x_3874_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_3875_; size_t v___x_3876_; size_t v___x_3877_; 
v___x_3875_ = ((size_t)5ULL);
v___x_3876_ = ((size_t)1ULL);
v___x_3877_ = lean_usize_shift_left(v___x_3876_, v___x_3875_);
return v___x_3877_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3878_; size_t v___x_3879_; size_t v___x_3880_; 
v___x_3878_ = ((size_t)1ULL);
v___x_3879_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3880_ = lean_usize_sub(v___x_3879_, v___x_3878_);
return v___x_3880_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3882_, size_t v_x_3883_, size_t v_x_3884_, lean_object* v_x_3885_, lean_object* v_x_3886_){
_start:
{
if (lean_obj_tag(v_x_3882_) == 0)
{
lean_object* v_es_3887_; size_t v___x_3888_; size_t v___x_3889_; size_t v___x_3890_; size_t v___x_3891_; lean_object* v_j_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v_es_3887_ = lean_ctor_get(v_x_3882_, 0);
v___x_3888_ = ((size_t)5ULL);
v___x_3889_ = ((size_t)1ULL);
v___x_3890_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1);
v___x_3891_ = lean_usize_land(v_x_3883_, v___x_3890_);
v_j_3892_ = lean_usize_to_nat(v___x_3891_);
v___x_3893_ = lean_array_get_size(v_es_3887_);
v___x_3894_ = lean_nat_dec_lt(v_j_3892_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_dec(v_j_3892_);
lean_dec(v_x_3886_);
lean_dec(v_x_3885_);
return v_x_3882_;
}
else
{
lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3931_; 
lean_inc_ref(v_es_3887_);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_x_3882_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_x_3882_, 0);
lean_dec(v_unused_3932_);
v___x_3896_ = v_x_3882_;
v_isShared_3897_ = v_isSharedCheck_3931_;
goto v_resetjp_3895_;
}
else
{
lean_dec(v_x_3882_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3931_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v_v_3898_; lean_object* v___x_3899_; lean_object* v_xs_x27_3900_; lean_object* v___y_3902_; 
v_v_3898_ = lean_array_fget(v_es_3887_, v_j_3892_);
v___x_3899_ = lean_box(0);
v_xs_x27_3900_ = lean_array_fset(v_es_3887_, v_j_3892_, v___x_3899_);
switch(lean_obj_tag(v_v_3898_))
{
case 0:
{
lean_object* v_key_3907_; lean_object* v_val_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3918_; 
v_key_3907_ = lean_ctor_get(v_v_3898_, 0);
v_val_3908_ = lean_ctor_get(v_v_3898_, 1);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_v_3898_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3910_ = v_v_3898_;
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_val_3908_);
lean_inc(v_key_3907_);
lean_dec(v_v_3898_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
uint8_t v___x_3912_; 
v___x_3912_ = l_Lean_instBEqMVarId_beq(v_x_3885_, v_key_3907_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_del_object(v___x_3910_);
v___x_3913_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3907_, v_val_3908_, v_x_3885_, v_x_3886_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
v___y_3902_ = v___x_3914_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3916_; 
lean_dec(v_val_3908_);
lean_dec(v_key_3907_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 1, v_x_3886_);
lean_ctor_set(v___x_3910_, 0, v_x_3885_);
v___x_3916_ = v___x_3910_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_x_3885_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_x_3886_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
v___y_3902_ = v___x_3916_;
goto v___jp_3901_;
}
}
}
}
case 1:
{
lean_object* v_node_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3929_; 
v_node_3919_ = lean_ctor_get(v_v_3898_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_v_3898_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3921_ = v_v_3898_;
v_isShared_3922_ = v_isSharedCheck_3929_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_node_3919_);
lean_dec(v_v_3898_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3929_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
size_t v___x_3923_; size_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3927_; 
v___x_3923_ = lean_usize_shift_right(v_x_3883_, v___x_3888_);
v___x_3924_ = lean_usize_add(v_x_3884_, v___x_3889_);
v___x_3925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3919_, v___x_3923_, v___x_3924_, v_x_3885_, v_x_3886_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3925_);
v___x_3927_ = v___x_3921_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
v___y_3902_ = v___x_3927_;
goto v___jp_3901_;
}
}
}
default: 
{
lean_object* v___x_3930_; 
v___x_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3930_, 0, v_x_3885_);
lean_ctor_set(v___x_3930_, 1, v_x_3886_);
v___y_3902_ = v___x_3930_;
goto v___jp_3901_;
}
}
v___jp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_array_fset(v_xs_x27_3900_, v_j_3892_, v___y_3902_);
lean_dec(v_j_3892_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3903_);
v___x_3905_ = v___x_3896_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
else
{
lean_object* v_ks_3933_; lean_object* v_vs_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3954_; 
v_ks_3933_ = lean_ctor_get(v_x_3882_, 0);
v_vs_3934_ = lean_ctor_get(v_x_3882_, 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_x_3882_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3936_ = v_x_3882_;
v_isShared_3937_ = v_isSharedCheck_3954_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_vs_3934_);
lean_inc(v_ks_3933_);
lean_dec(v_x_3882_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3954_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_ks_3933_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_vs_3934_);
v___x_3939_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v_newNode_3940_; uint8_t v___y_3942_; size_t v___x_3948_; uint8_t v___x_3949_; 
v_newNode_3940_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3939_, v_x_3885_, v_x_3886_);
v___x_3948_ = ((size_t)7ULL);
v___x_3949_ = lean_usize_dec_le(v___x_3948_, v_x_3884_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3950_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3940_);
v___x_3951_ = lean_unsigned_to_nat(4u);
v___x_3952_ = lean_nat_dec_lt(v___x_3950_, v___x_3951_);
lean_dec(v___x_3950_);
v___y_3942_ = v___x_3952_;
goto v___jp_3941_;
}
else
{
v___y_3942_ = v___x_3949_;
goto v___jp_3941_;
}
v___jp_3941_:
{
if (v___y_3942_ == 0)
{
lean_object* v_ks_3943_; lean_object* v_vs_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_ks_3943_ = lean_ctor_get(v_newNode_3940_, 0);
lean_inc_ref(v_ks_3943_);
v_vs_3944_ = lean_ctor_get(v_newNode_3940_, 1);
lean_inc_ref(v_vs_3944_);
lean_dec_ref(v_newNode_3940_);
v___x_3945_ = lean_unsigned_to_nat(0u);
v___x_3946_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_3947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3884_, v_ks_3943_, v_vs_3944_, v___x_3945_, v___x_3946_);
lean_dec_ref(v_vs_3944_);
lean_dec_ref(v_ks_3943_);
return v___x_3947_;
}
else
{
return v_newNode_3940_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3955_, lean_object* v_keys_3956_, lean_object* v_vals_3957_, lean_object* v_i_3958_, lean_object* v_entries_3959_){
_start:
{
lean_object* v___x_3960_; uint8_t v___x_3961_; 
v___x_3960_ = lean_array_get_size(v_keys_3956_);
v___x_3961_ = lean_nat_dec_lt(v_i_3958_, v___x_3960_);
if (v___x_3961_ == 0)
{
lean_dec(v_i_3958_);
return v_entries_3959_;
}
else
{
lean_object* v_k_3962_; lean_object* v_v_3963_; uint64_t v___x_3964_; size_t v_h_3965_; size_t v___x_3966_; lean_object* v___x_3967_; size_t v___x_3968_; size_t v___x_3969_; size_t v___x_3970_; size_t v_h_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_k_3962_ = lean_array_fget_borrowed(v_keys_3956_, v_i_3958_);
v_v_3963_ = lean_array_fget_borrowed(v_vals_3957_, v_i_3958_);
v___x_3964_ = l_Lean_instHashableMVarId_hash(v_k_3962_);
v_h_3965_ = lean_uint64_to_usize(v___x_3964_);
v___x_3966_ = ((size_t)5ULL);
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = ((size_t)1ULL);
v___x_3969_ = lean_usize_sub(v_depth_3955_, v___x_3968_);
v___x_3970_ = lean_usize_mul(v___x_3966_, v___x_3969_);
v_h_3971_ = lean_usize_shift_right(v_h_3965_, v___x_3970_);
v___x_3972_ = lean_nat_add(v_i_3958_, v___x_3967_);
lean_dec(v_i_3958_);
lean_inc(v_v_3963_);
lean_inc(v_k_3962_);
v___x_3973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3959_, v_h_3971_, v_depth_3955_, v_k_3962_, v_v_3963_);
v_i_3958_ = v___x_3972_;
v_entries_3959_ = v___x_3973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3975_, lean_object* v_keys_3976_, lean_object* v_vals_3977_, lean_object* v_i_3978_, lean_object* v_entries_3979_){
_start:
{
size_t v_depth_boxed_3980_; lean_object* v_res_3981_; 
v_depth_boxed_3980_ = lean_unbox_usize(v_depth_3975_);
lean_dec(v_depth_3975_);
v_res_3981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3980_, v_keys_3976_, v_vals_3977_, v_i_3978_, v_entries_3979_);
lean_dec_ref(v_vals_3977_);
lean_dec_ref(v_keys_3976_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3982_, lean_object* v_x_3983_, lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_){
_start:
{
size_t v_x_2319__boxed_3987_; size_t v_x_2320__boxed_3988_; lean_object* v_res_3989_; 
v_x_2319__boxed_3987_ = lean_unbox_usize(v_x_3983_);
lean_dec(v_x_3983_);
v_x_2320__boxed_3988_ = lean_unbox_usize(v_x_3984_);
lean_dec(v_x_3984_);
v_res_3989_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3982_, v_x_2319__boxed_3987_, v_x_2320__boxed_3988_, v_x_3985_, v_x_3986_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3990_, lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
uint64_t v___x_3993_; size_t v___x_3994_; size_t v___x_3995_; lean_object* v___x_3996_; 
v___x_3993_ = l_Lean_instHashableMVarId_hash(v_x_3991_);
v___x_3994_ = lean_uint64_to_usize(v___x_3993_);
v___x_3995_ = ((size_t)1ULL);
v___x_3996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3990_, v___x_3994_, v___x_3995_, v_x_3991_, v_x_3992_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_3997_, lean_object* v_val_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4001_; lean_object* v_mctx_4002_; lean_object* v_cache_4003_; lean_object* v_zetaDeltaFVarIds_4004_; lean_object* v_postponed_4005_; lean_object* v_diag_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4033_; 
v___x_4001_ = lean_st_ref_take(v___y_3999_);
v_mctx_4002_ = lean_ctor_get(v___x_4001_, 0);
v_cache_4003_ = lean_ctor_get(v___x_4001_, 1);
v_zetaDeltaFVarIds_4004_ = lean_ctor_get(v___x_4001_, 2);
v_postponed_4005_ = lean_ctor_get(v___x_4001_, 3);
v_diag_4006_ = lean_ctor_get(v___x_4001_, 4);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4008_ = v___x_4001_;
v_isShared_4009_ = v_isSharedCheck_4033_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_diag_4006_);
lean_inc(v_postponed_4005_);
lean_inc(v_zetaDeltaFVarIds_4004_);
lean_inc(v_cache_4003_);
lean_inc(v_mctx_4002_);
lean_dec(v___x_4001_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4033_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v_depth_4010_; lean_object* v_levelAssignDepth_4011_; lean_object* v_mvarCounter_4012_; lean_object* v_lDepth_4013_; lean_object* v_decls_4014_; lean_object* v_userNames_4015_; lean_object* v_lAssignment_4016_; lean_object* v_eAssignment_4017_; lean_object* v_dAssignment_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4032_; 
v_depth_4010_ = lean_ctor_get(v_mctx_4002_, 0);
v_levelAssignDepth_4011_ = lean_ctor_get(v_mctx_4002_, 1);
v_mvarCounter_4012_ = lean_ctor_get(v_mctx_4002_, 2);
v_lDepth_4013_ = lean_ctor_get(v_mctx_4002_, 3);
v_decls_4014_ = lean_ctor_get(v_mctx_4002_, 4);
v_userNames_4015_ = lean_ctor_get(v_mctx_4002_, 5);
v_lAssignment_4016_ = lean_ctor_get(v_mctx_4002_, 6);
v_eAssignment_4017_ = lean_ctor_get(v_mctx_4002_, 7);
v_dAssignment_4018_ = lean_ctor_get(v_mctx_4002_, 8);
v_isSharedCheck_4032_ = !lean_is_exclusive(v_mctx_4002_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4020_ = v_mctx_4002_;
v_isShared_4021_ = v_isSharedCheck_4032_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_dAssignment_4018_);
lean_inc(v_eAssignment_4017_);
lean_inc(v_lAssignment_4016_);
lean_inc(v_userNames_4015_);
lean_inc(v_decls_4014_);
lean_inc(v_lDepth_4013_);
lean_inc(v_mvarCounter_4012_);
lean_inc(v_levelAssignDepth_4011_);
lean_inc(v_depth_4010_);
lean_dec(v_mctx_4002_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4032_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4022_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_4017_, v_mvarId_3997_, v_val_3998_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 7, v___x_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_depth_4010_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_levelAssignDepth_4011_);
lean_ctor_set(v_reuseFailAlloc_4031_, 2, v_mvarCounter_4012_);
lean_ctor_set(v_reuseFailAlloc_4031_, 3, v_lDepth_4013_);
lean_ctor_set(v_reuseFailAlloc_4031_, 4, v_decls_4014_);
lean_ctor_set(v_reuseFailAlloc_4031_, 5, v_userNames_4015_);
lean_ctor_set(v_reuseFailAlloc_4031_, 6, v_lAssignment_4016_);
lean_ctor_set(v_reuseFailAlloc_4031_, 7, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4031_, 8, v_dAssignment_4018_);
v___x_4024_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4026_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4024_);
v___x_4026_ = v___x_4008_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_cache_4003_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_zetaDeltaFVarIds_4004_);
lean_ctor_set(v_reuseFailAlloc_4030_, 3, v_postponed_4005_);
lean_ctor_set(v_reuseFailAlloc_4030_, 4, v_diag_4006_);
v___x_4026_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = lean_st_ref_set(v___y_3999_, v___x_4026_);
v___x_4028_ = lean_box(0);
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
return v___x_4029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4034_, lean_object* v_val_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4034_, v_val_4035_, v___y_4036_);
lean_dec(v___y_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4039_, size_t v_i_4040_, lean_object* v_bs_4041_){
_start:
{
uint8_t v___x_4042_; 
v___x_4042_ = lean_usize_dec_lt(v_i_4040_, v_sz_4039_);
if (v___x_4042_ == 0)
{
return v_bs_4041_;
}
else
{
lean_object* v_v_4043_; lean_object* v___x_4044_; lean_object* v_bs_x27_4045_; lean_object* v___x_4046_; size_t v___x_4047_; size_t v___x_4048_; lean_object* v___x_4049_; 
v_v_4043_ = lean_array_uget(v_bs_4041_, v_i_4040_);
v___x_4044_ = lean_unsigned_to_nat(0u);
v_bs_x27_4045_ = lean_array_uset(v_bs_4041_, v_i_4040_, v___x_4044_);
v___x_4046_ = l_Lean_Expr_fvar___override(v_v_4043_);
v___x_4047_ = ((size_t)1ULL);
v___x_4048_ = lean_usize_add(v_i_4040_, v___x_4047_);
v___x_4049_ = lean_array_uset(v_bs_x27_4045_, v_i_4040_, v___x_4046_);
v_i_4040_ = v___x_4048_;
v_bs_4041_ = v___x_4049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4051_, lean_object* v_i_4052_, lean_object* v_bs_4053_){
_start:
{
size_t v_sz_boxed_4054_; size_t v_i_boxed_4055_; lean_object* v_res_4056_; 
v_sz_boxed_4054_ = lean_unbox_usize(v_sz_4051_);
lean_dec(v_sz_4051_);
v_i_boxed_4055_ = lean_unbox_usize(v_i_4052_);
lean_dec(v_i_4052_);
v_res_4056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4054_, v_i_boxed_4055_, v_bs_4053_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4057_, lean_object* v_mvarId_4058_, lean_object* v___x_4059_, lean_object* v_a_4060_, lean_object* v_fvarIds_4061_, lean_object* v_es_4062_, lean_object* v_givenNames_x27_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; uint8_t v___y_4121_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = lean_array_get_borrowed(v___x_4057_, v_es_4062_, v___x_4069_);
v___x_4131_ = lean_array_get_size(v_fvarIds_4061_);
v___x_4132_ = lean_nat_dec_eq(v___x_4131_, v___x_4069_);
if (v___x_4132_ == 0)
{
v___y_4121_ = v___x_4132_;
goto v___jp_4120_;
}
else
{
uint8_t v___x_4133_; 
v___x_4133_ = lean_expr_eqv(v_a_4060_, v___x_4070_);
v___y_4121_ = v___x_4133_;
goto v___jp_4120_;
}
v___jp_4071_:
{
lean_object* v___x_4072_; 
lean_inc(v_mvarId_4058_);
v___x_4072_ = l_Lean_MVarId_getTag(v_mvarId_4058_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4074_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref(v___x_4072_);
lean_inc(v___x_4070_);
v___x_4074_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4070_, v_a_4073_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; size_t v_sz_4076_; size_t v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; uint8_t v___x_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref(v___x_4074_);
v_sz_4076_ = lean_array_size(v_fvarIds_4061_);
v___x_4077_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4061_);
v___x_4078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4076_, v___x_4077_, v_fvarIds_4061_);
v___x_4079_ = 0;
v___x_4080_ = 1;
v___x_4081_ = 1;
lean_inc(v_a_4075_);
v___x_4082_ = l_Lean_Meta_mkLetFVars(v___x_4078_, v_a_4075_, v___x_4079_, v___x_4080_, v___x_4081_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec_ref(v___x_4078_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4094_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref(v___x_4082_);
v___x_4084_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4058_, v_a_4083_, v___y_4065_);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; 
v_unused_4095_ = lean_ctor_get(v___x_4084_, 0);
lean_dec(v_unused_4095_);
v___x_4086_ = v___x_4084_;
v_isShared_4087_ = v_isSharedCheck_4094_;
goto v_resetjp_4085_;
}
else
{
lean_dec(v___x_4084_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4094_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4092_; 
v___x_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4088_, 0, v_fvarIds_4061_);
lean_ctor_set(v___x_4088_, 1, v_givenNames_x27_4063_);
v___x_4089_ = l_Lean_Expr_mvarId_x21(v_a_4075_);
lean_dec(v_a_4075_);
v___x_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 0, v___x_4090_);
v___x_4092_ = v___x_4086_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_a_4075_);
lean_dec(v_givenNames_x27_4063_);
lean_dec_ref(v_fvarIds_4061_);
lean_dec(v_mvarId_4058_);
v_a_4096_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4082_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4082_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v_givenNames_x27_4063_);
lean_dec_ref(v_fvarIds_4061_);
lean_dec(v_mvarId_4058_);
v_a_4104_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4074_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4074_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec(v_givenNames_x27_4063_);
lean_dec_ref(v_fvarIds_4061_);
lean_dec(v_mvarId_4058_);
v_a_4112_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4072_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4072_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
v___jp_4120_:
{
if (v___y_4121_ == 0)
{
lean_dec(v___x_4059_);
goto v___jp_4071_;
}
else
{
lean_object* v___x_4122_; 
lean_inc(v_mvarId_4058_);
v___x_4122_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4059_, v_mvarId_4058_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_dec_ref(v___x_4122_);
goto v___jp_4071_;
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_givenNames_x27_4063_);
lean_dec_ref(v_fvarIds_4061_);
lean_dec(v_mvarId_4058_);
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4134_, lean_object* v_mvarId_4135_, lean_object* v___x_4136_, lean_object* v_a_4137_, lean_object* v_fvarIds_4138_, lean_object* v_es_4139_, lean_object* v_givenNames_x27_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_MVarId_extractLets___lam__0(v___x_4134_, v_mvarId_4135_, v___x_4136_, v_a_4137_, v_fvarIds_4138_, v_es_4139_, v_givenNames_x27_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec_ref(v_es_4139_);
lean_dec_ref(v_a_4137_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4147_, lean_object* v___x_4148_, lean_object* v___x_4149_, lean_object* v_givenNames_4150_, lean_object* v_config_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___x_4157_; 
lean_inc(v___x_4148_);
lean_inc(v_mvarId_4147_);
v___x_4157_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4147_, v___x_4148_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4158_; 
lean_dec_ref(v___x_4157_);
lean_inc(v_mvarId_4147_);
v___x_4158_ = l_Lean_MVarId_getType(v_mvarId_4147_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___f_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref(v___x_4158_);
lean_inc(v_a_4159_);
v___f_4160_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4160_, 0, v___x_4149_);
lean_closure_set(v___f_4160_, 1, v_mvarId_4147_);
lean_closure_set(v___f_4160_, 2, v___x_4148_);
lean_closure_set(v___f_4160_, 3, v_a_4159_);
v___x_4161_ = lean_unsigned_to_nat(1u);
v___x_4162_ = lean_mk_empty_array_with_capacity(v___x_4161_);
v___x_4163_ = lean_array_push(v___x_4162_, v_a_4159_);
v___x_4164_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4163_, v_givenNames_4150_, v___f_4160_, v_config_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
return v___x_4164_;
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v_givenNames_4150_);
lean_dec_ref(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v_mvarId_4147_);
v_a_4165_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4158_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4158_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec(v_givenNames_4150_);
lean_dec_ref(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v_mvarId_4147_);
v_a_4173_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4157_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4157_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v_givenNames_4184_, lean_object* v_config_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4181_, v___x_4182_, v___x_4183_, v_givenNames_4184_, v_config_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec_ref(v_config_4185_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4195_, lean_object* v_givenNames_4196_, lean_object* v_config_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___f_4205_; lean_object* v___x_4206_; 
v___x_4203_ = l_Lean_instInhabitedExpr;
v___x_4204_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4195_);
v___f_4205_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4205_, 0, v_mvarId_4195_);
lean_closure_set(v___f_4205_, 1, v___x_4204_);
lean_closure_set(v___f_4205_, 2, v___x_4203_);
lean_closure_set(v___f_4205_, 3, v_givenNames_4196_);
lean_closure_set(v___f_4205_, 4, v_config_4197_);
v___x_4206_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4195_, v___f_4205_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4207_, lean_object* v_givenNames_4208_, lean_object* v_config_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_MVarId_extractLets(v_mvarId_4207_, v_givenNames_4208_, v_config_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4216_, lean_object* v_val_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4216_, v_val_4217_, v___y_4219_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4224_, lean_object* v_val_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4224_, v_val_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4232_, lean_object* v_x_4233_, lean_object* v_x_4234_, lean_object* v_x_4235_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4233_, v_x_4234_, v_x_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4237_, lean_object* v_x_4238_, size_t v_x_4239_, size_t v_x_4240_, lean_object* v_x_4241_, lean_object* v_x_4242_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4238_, v_x_4239_, v_x_4240_, v_x_4241_, v_x_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4244_, lean_object* v_x_4245_, lean_object* v_x_4246_, lean_object* v_x_4247_, lean_object* v_x_4248_, lean_object* v_x_4249_){
_start:
{
size_t v_x_2823__boxed_4250_; size_t v_x_2824__boxed_4251_; lean_object* v_res_4252_; 
v_x_2823__boxed_4250_ = lean_unbox_usize(v_x_4246_);
lean_dec(v_x_4246_);
v_x_2824__boxed_4251_ = lean_unbox_usize(v_x_4247_);
lean_dec(v_x_4247_);
v_res_4252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4244_, v_x_4245_, v_x_2823__boxed_4250_, v_x_2824__boxed_4251_, v_x_4248_, v_x_4249_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4253_, lean_object* v_n_4254_, lean_object* v_k_4255_, lean_object* v_v_4256_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4254_, v_k_4255_, v_v_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4258_, size_t v_depth_4259_, lean_object* v_keys_4260_, lean_object* v_vals_4261_, lean_object* v_heq_4262_, lean_object* v_i_4263_, lean_object* v_entries_4264_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4259_, v_keys_4260_, v_vals_4261_, v_i_4263_, v_entries_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4266_, lean_object* v_depth_4267_, lean_object* v_keys_4268_, lean_object* v_vals_4269_, lean_object* v_heq_4270_, lean_object* v_i_4271_, lean_object* v_entries_4272_){
_start:
{
size_t v_depth_boxed_4273_; lean_object* v_res_4274_; 
v_depth_boxed_4273_ = lean_unbox_usize(v_depth_4267_);
lean_dec(v_depth_4267_);
v_res_4274_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4266_, v_depth_boxed_4273_, v_keys_4268_, v_vals_4269_, v_heq_4270_, v_i_4271_, v_entries_4272_);
lean_dec_ref(v_vals_4269_);
lean_dec_ref(v_keys_4268_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4275_, lean_object* v_x_4276_, lean_object* v_x_4277_, lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4276_, v_x_4277_, v_x_4278_, v_x_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4281_, size_t v_i_4282_, lean_object* v_bs_4283_){
_start:
{
uint8_t v___x_4284_; 
v___x_4284_ = lean_usize_dec_lt(v_i_4282_, v_sz_4281_);
if (v___x_4284_ == 0)
{
return v_bs_4283_;
}
else
{
lean_object* v_v_4285_; lean_object* v___x_4286_; lean_object* v_bs_x27_4287_; lean_object* v___x_4288_; size_t v___x_4289_; size_t v___x_4290_; lean_object* v___x_4291_; 
v_v_4285_ = lean_array_uget(v_bs_4283_, v_i_4282_);
v___x_4286_ = lean_unsigned_to_nat(0u);
v_bs_x27_4287_ = lean_array_uset(v_bs_4283_, v_i_4282_, v___x_4286_);
v___x_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4288_, 0, v_v_4285_);
v___x_4289_ = ((size_t)1ULL);
v___x_4290_ = lean_usize_add(v_i_4282_, v___x_4289_);
v___x_4291_ = lean_array_uset(v_bs_x27_4287_, v_i_4282_, v___x_4288_);
v_i_4282_ = v___x_4290_;
v_bs_4283_ = v___x_4291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4293_, lean_object* v_i_4294_, lean_object* v_bs_4295_){
_start:
{
size_t v_sz_boxed_4296_; size_t v_i_boxed_4297_; lean_object* v_res_4298_; 
v_sz_boxed_4296_ = lean_unbox_usize(v_sz_4293_);
lean_dec(v_sz_4293_);
v_i_boxed_4297_ = lean_unbox_usize(v_i_4294_);
lean_dec(v_i_4294_);
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4296_, v_i_boxed_4297_, v_bs_4295_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4299_, lean_object* v_fvars_4300_, lean_object* v_fvarIds_4301_, lean_object* v_givenNames_x27_4302_, lean_object* v_targetNew_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; 
lean_inc(v_mvarId_4299_);
v___x_4309_ = l_Lean_MVarId_getTag(v_mvarId_4299_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref(v___x_4309_);
v___x_4311_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4303_, v_a_4310_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; size_t v_sz_4313_; size_t v___x_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; uint8_t v___x_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref(v___x_4311_);
v_sz_4313_ = lean_array_size(v_fvarIds_4301_);
v___x_4314_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4301_);
v___x_4315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4313_, v___x_4314_, v_fvarIds_4301_);
v___x_4316_ = 0;
v___x_4317_ = 1;
v___x_4318_ = 1;
lean_inc(v_a_4312_);
v___x_4319_ = l_Lean_Meta_mkLetFVars(v___x_4315_, v_a_4312_, v___x_4316_, v___x_4317_, v___x_4318_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec_ref(v___x_4315_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4334_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref(v___x_4319_);
v___x_4321_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4299_, v_a_4320_, v___y_4305_);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4334_ == 0)
{
lean_object* v_unused_4335_; 
v_unused_4335_ = lean_ctor_get(v___x_4321_, 0);
lean_dec(v_unused_4335_);
v___x_4323_ = v___x_4321_;
v_isShared_4324_ = v_isSharedCheck_4334_;
goto v_resetjp_4322_;
}
else
{
lean_dec(v___x_4321_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4334_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; size_t v_sz_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4332_; 
v___x_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4325_, 0, v_fvarIds_4301_);
lean_ctor_set(v___x_4325_, 1, v_givenNames_x27_4302_);
v_sz_4326_ = lean_array_size(v_fvars_4300_);
v___x_4327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4326_, v___x_4314_, v_fvars_4300_);
v___x_4328_ = l_Lean_Expr_mvarId_x21(v_a_4312_);
lean_dec(v_a_4312_);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4325_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 0, v___x_4330_);
v___x_4332_ = v___x_4323_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4330_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v_a_4312_);
lean_dec(v_givenNames_x27_4302_);
lean_dec_ref(v_fvarIds_4301_);
lean_dec_ref(v_fvars_4300_);
lean_dec(v_mvarId_4299_);
v_a_4336_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4319_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4319_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_givenNames_x27_4302_);
lean_dec_ref(v_fvarIds_4301_);
lean_dec_ref(v_fvars_4300_);
lean_dec(v_mvarId_4299_);
v_a_4344_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4311_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4311_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec_ref(v_targetNew_4303_);
lean_dec(v_givenNames_x27_4302_);
lean_dec_ref(v_fvarIds_4301_);
lean_dec_ref(v_fvars_4300_);
lean_dec(v_mvarId_4299_);
v_a_4352_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4309_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4309_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4360_, lean_object* v_fvars_4361_, lean_object* v_fvarIds_4362_, lean_object* v_givenNames_x27_4363_, lean_object* v_targetNew_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4360_, v_fvars_4361_, v_fvarIds_4362_, v_givenNames_x27_4363_, v_targetNew_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4371_, lean_object* v_binderName_4372_, lean_object* v_body_4373_, uint8_t v_binderInfo_4374_, lean_object* v___f_4375_, lean_object* v___x_4376_, lean_object* v_mvarId_4377_, lean_object* v_binderType_4378_, lean_object* v_fvarIds_4379_, lean_object* v_es_4380_, lean_object* v_givenNames_x27_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___y_4393_; lean_object* v___x_4403_; uint8_t v___x_4404_; 
v___x_4387_ = lean_unsigned_to_nat(0u);
v___x_4388_ = lean_array_get_borrowed(v___x_4371_, v_es_4380_, v___x_4387_);
v___x_4403_ = lean_array_get_size(v_fvarIds_4379_);
v___x_4404_ = lean_nat_dec_eq(v___x_4403_, v___x_4387_);
if (v___x_4404_ == 0)
{
v___y_4393_ = v___x_4404_;
goto v___jp_4392_;
}
else
{
uint8_t v___x_4405_; 
v___x_4405_ = lean_expr_eqv(v_binderType_4378_, v___x_4388_);
v___y_4393_ = v___x_4405_;
goto v___jp_4392_;
}
v___jp_4389_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
lean_inc(v___x_4388_);
v___x_4390_ = l_Lean_Expr_forallE___override(v_binderName_4372_, v___x_4388_, v_body_4373_, v_binderInfo_4374_);
lean_inc(v___y_4385_);
lean_inc_ref(v___y_4384_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
v___x_4391_ = lean_apply_8(v___f_4375_, v_fvarIds_4379_, v_givenNames_x27_4381_, v___x_4390_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, lean_box(0));
return v___x_4391_;
}
v___jp_4392_:
{
if (v___y_4393_ == 0)
{
lean_dec(v_mvarId_4377_);
lean_dec(v___x_4376_);
goto v___jp_4389_;
}
else
{
lean_object* v___x_4394_; 
v___x_4394_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4376_, v_mvarId_4377_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_dec_ref(v___x_4394_);
goto v___jp_4389_;
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec(v_givenNames_x27_4381_);
lean_dec_ref(v_fvarIds_4379_);
lean_dec_ref(v___f_4375_);
lean_dec_ref(v_body_4373_);
lean_dec(v_binderName_4372_);
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4406_, lean_object* v_binderName_4407_, lean_object* v_body_4408_, lean_object* v_binderInfo_4409_, lean_object* v___f_4410_, lean_object* v___x_4411_, lean_object* v_mvarId_4412_, lean_object* v_binderType_4413_, lean_object* v_fvarIds_4414_, lean_object* v_es_4415_, lean_object* v_givenNames_x27_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v_binderInfo_1852__boxed_4422_; lean_object* v_res_4423_; 
v_binderInfo_1852__boxed_4422_ = lean_unbox(v_binderInfo_4409_);
v_res_4423_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4406_, v_binderName_4407_, v_body_4408_, v_binderInfo_1852__boxed_4422_, v___f_4410_, v___x_4411_, v_mvarId_4412_, v_binderType_4413_, v_fvarIds_4414_, v_es_4415_, v_givenNames_x27_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec_ref(v_es_4415_);
lean_dec_ref(v_binderType_4413_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4424_, lean_object* v_declName_4425_, lean_object* v_body_4426_, uint8_t v_nondep_4427_, lean_object* v___f_4428_, lean_object* v_value_4429_, lean_object* v___x_4430_, lean_object* v_mvarId_4431_, lean_object* v_type_4432_, lean_object* v_fvarIds_4433_, lean_object* v_es_4434_, lean_object* v_givenNames_x27_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; uint8_t v___y_4449_; lean_object* v___x_4460_; uint8_t v___x_4461_; 
v___x_4441_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_4424_);
v___x_4442_ = lean_array_get_borrowed(v___x_4424_, v_es_4434_, v___x_4441_);
v___x_4443_ = lean_unsigned_to_nat(1u);
v___x_4444_ = lean_array_get_borrowed(v___x_4424_, v_es_4434_, v___x_4443_);
v___x_4460_ = lean_array_get_size(v_fvarIds_4433_);
v___x_4461_ = lean_nat_dec_eq(v___x_4460_, v___x_4441_);
if (v___x_4461_ == 0)
{
v___y_4449_ = v___x_4461_;
goto v___jp_4448_;
}
else
{
uint8_t v___x_4462_; 
v___x_4462_ = lean_expr_eqv(v_type_4432_, v___x_4442_);
v___y_4449_ = v___x_4462_;
goto v___jp_4448_;
}
v___jp_4445_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
lean_inc(v___x_4444_);
lean_inc(v___x_4442_);
v___x_4446_ = l_Lean_Expr_letE___override(v_declName_4425_, v___x_4442_, v___x_4444_, v_body_4426_, v_nondep_4427_);
lean_inc(v___y_4439_);
lean_inc_ref(v___y_4438_);
lean_inc(v___y_4437_);
lean_inc_ref(v___y_4436_);
v___x_4447_ = lean_apply_8(v___f_4428_, v_fvarIds_4433_, v_givenNames_x27_4435_, v___x_4446_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, lean_box(0));
return v___x_4447_;
}
v___jp_4448_:
{
if (v___y_4449_ == 0)
{
lean_dec(v_mvarId_4431_);
lean_dec(v___x_4430_);
goto v___jp_4445_;
}
else
{
uint8_t v___x_4450_; 
v___x_4450_ = lean_expr_eqv(v_value_4429_, v___x_4444_);
if (v___x_4450_ == 0)
{
lean_dec(v_mvarId_4431_);
lean_dec(v___x_4430_);
goto v___jp_4445_;
}
else
{
lean_object* v___x_4451_; 
v___x_4451_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4430_, v_mvarId_4431_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_dec_ref(v___x_4451_);
goto v___jp_4445_;
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_givenNames_x27_4435_);
lean_dec_ref(v_fvarIds_4433_);
lean_dec_ref(v___f_4428_);
lean_dec_ref(v_body_4426_);
lean_dec(v_declName_4425_);
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4451_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4463_ = _args[0];
lean_object* v_declName_4464_ = _args[1];
lean_object* v_body_4465_ = _args[2];
lean_object* v_nondep_4466_ = _args[3];
lean_object* v___f_4467_ = _args[4];
lean_object* v_value_4468_ = _args[5];
lean_object* v___x_4469_ = _args[6];
lean_object* v_mvarId_4470_ = _args[7];
lean_object* v_type_4471_ = _args[8];
lean_object* v_fvarIds_4472_ = _args[9];
lean_object* v_es_4473_ = _args[10];
lean_object* v_givenNames_x27_4474_ = _args[11];
lean_object* v___y_4475_ = _args[12];
lean_object* v___y_4476_ = _args[13];
lean_object* v___y_4477_ = _args[14];
lean_object* v___y_4478_ = _args[15];
lean_object* v___y_4479_ = _args[16];
_start:
{
uint8_t v_nondep_1927__boxed_4480_; lean_object* v_res_4481_; 
v_nondep_1927__boxed_4480_ = lean_unbox(v_nondep_4466_);
v_res_4481_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4463_, v_declName_4464_, v_body_4465_, v_nondep_1927__boxed_4480_, v___f_4467_, v_value_4468_, v___x_4469_, v_mvarId_4470_, v_type_4471_, v_fvarIds_4472_, v_es_4473_, v_givenNames_x27_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec_ref(v_es_4473_);
lean_dec_ref(v_type_4471_);
lean_dec_ref(v_value_4468_);
return v_res_4481_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4485_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4486_ = l_Lean_MessageData_ofFormat(v___x_4485_);
return v___x_4486_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4489_, lean_object* v___x_4490_, lean_object* v___f_4491_, lean_object* v___x_4492_, lean_object* v_givenNames_4493_, lean_object* v_config_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; 
lean_inc(v_mvarId_4489_);
v___x_4500_ = l_Lean_MVarId_getType(v_mvarId_4489_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref(v___x_4500_);
switch(lean_obj_tag(v_a_4501_))
{
case 7:
{
lean_object* v_binderName_4502_; lean_object* v_binderType_4503_; lean_object* v_body_4504_; uint8_t v_binderInfo_4505_; lean_object* v___x_4506_; lean_object* v___f_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v_binderName_4502_ = lean_ctor_get(v_a_4501_, 0);
lean_inc(v_binderName_4502_);
v_binderType_4503_ = lean_ctor_get(v_a_4501_, 1);
lean_inc_ref(v_binderType_4503_);
v_body_4504_ = lean_ctor_get(v_a_4501_, 2);
lean_inc_ref(v_body_4504_);
v_binderInfo_4505_ = lean_ctor_get_uint8(v_a_4501_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4501_);
v___x_4506_ = lean_box(v_binderInfo_4505_);
lean_inc_ref(v_binderType_4503_);
v___f_4507_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4507_, 0, v___x_4490_);
lean_closure_set(v___f_4507_, 1, v_binderName_4502_);
lean_closure_set(v___f_4507_, 2, v_body_4504_);
lean_closure_set(v___f_4507_, 3, v___x_4506_);
lean_closure_set(v___f_4507_, 4, v___f_4491_);
lean_closure_set(v___f_4507_, 5, v___x_4492_);
lean_closure_set(v___f_4507_, 6, v_mvarId_4489_);
lean_closure_set(v___f_4507_, 7, v_binderType_4503_);
v___x_4508_ = lean_unsigned_to_nat(1u);
v___x_4509_ = lean_mk_empty_array_with_capacity(v___x_4508_);
v___x_4510_ = lean_array_push(v___x_4509_, v_binderType_4503_);
v___x_4511_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4510_, v_givenNames_4493_, v___f_4507_, v_config_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4511_;
}
case 8:
{
lean_object* v_declName_4512_; lean_object* v_type_4513_; lean_object* v_value_4514_; lean_object* v_body_4515_; uint8_t v_nondep_4516_; lean_object* v___x_4517_; lean_object* v___f_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v_declName_4512_ = lean_ctor_get(v_a_4501_, 0);
lean_inc(v_declName_4512_);
v_type_4513_ = lean_ctor_get(v_a_4501_, 1);
lean_inc_ref(v_type_4513_);
v_value_4514_ = lean_ctor_get(v_a_4501_, 2);
lean_inc_ref(v_value_4514_);
v_body_4515_ = lean_ctor_get(v_a_4501_, 3);
lean_inc_ref(v_body_4515_);
v_nondep_4516_ = lean_ctor_get_uint8(v_a_4501_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4501_);
v___x_4517_ = lean_box(v_nondep_4516_);
lean_inc_ref(v_type_4513_);
lean_inc_ref(v_value_4514_);
v___f_4518_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4518_, 0, v___x_4490_);
lean_closure_set(v___f_4518_, 1, v_declName_4512_);
lean_closure_set(v___f_4518_, 2, v_body_4515_);
lean_closure_set(v___f_4518_, 3, v___x_4517_);
lean_closure_set(v___f_4518_, 4, v___f_4491_);
lean_closure_set(v___f_4518_, 5, v_value_4514_);
lean_closure_set(v___f_4518_, 6, v___x_4492_);
lean_closure_set(v___f_4518_, 7, v_mvarId_4489_);
lean_closure_set(v___f_4518_, 8, v_type_4513_);
v___x_4519_ = lean_unsigned_to_nat(2u);
v___x_4520_ = lean_mk_empty_array_with_capacity(v___x_4519_);
v___x_4521_ = lean_array_push(v___x_4520_, v_type_4513_);
v___x_4522_ = lean_array_push(v___x_4521_, v_value_4514_);
v___x_4523_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4522_, v_givenNames_4493_, v___f_4518_, v_config_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4523_;
}
default: 
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
lean_dec(v_a_4501_);
lean_dec(v_givenNames_4493_);
lean_dec_ref(v___f_4491_);
lean_dec_ref(v___x_4490_);
v___x_4524_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4525_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4492_, v_mvarId_4489_, v___x_4524_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4525_;
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_givenNames_4493_);
lean_dec(v___x_4492_);
lean_dec_ref(v___f_4491_);
lean_dec_ref(v___x_4490_);
lean_dec(v_mvarId_4489_);
v_a_4526_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4500_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4500_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4534_, lean_object* v___x_4535_, lean_object* v___f_4536_, lean_object* v___x_4537_, lean_object* v_givenNames_4538_, lean_object* v_config_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4534_, v___x_4535_, v___f_4536_, v___x_4537_, v_givenNames_4538_, v_config_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec_ref(v_config_4539_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4546_, lean_object* v___x_4547_, lean_object* v_givenNames_4548_, lean_object* v_config_4549_, lean_object* v_mvarId_4550_, lean_object* v_fvars_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v___f_4557_; lean_object* v___f_4558_; lean_object* v___x_4559_; 
lean_inc(v_mvarId_4550_);
v___f_4557_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4557_, 0, v_mvarId_4550_);
lean_closure_set(v___f_4557_, 1, v_fvars_4551_);
lean_inc(v_mvarId_4550_);
v___f_4558_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4558_, 0, v_mvarId_4550_);
lean_closure_set(v___f_4558_, 1, v___x_4546_);
lean_closure_set(v___f_4558_, 2, v___f_4557_);
lean_closure_set(v___f_4558_, 3, v___x_4547_);
lean_closure_set(v___f_4558_, 4, v_givenNames_4548_);
lean_closure_set(v___f_4558_, 5, v_config_4549_);
v___x_4559_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4550_, v___f_4558_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4560_, lean_object* v___x_4561_, lean_object* v_givenNames_4562_, lean_object* v_config_4563_, lean_object* v_mvarId_4564_, lean_object* v_fvars_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4560_, v___x_4561_, v_givenNames_4562_, v_config_4563_, v_mvarId_4564_, v_fvars_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4572_, lean_object* v_fvarId_4573_, lean_object* v_givenNames_4574_, lean_object* v_config_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4572_);
v___x_4582_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4572_, v___x_4581_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v___x_4583_; lean_object* v___f_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; uint8_t v___x_4588_; lean_object* v___x_4589_; 
lean_dec_ref(v___x_4582_);
v___x_4583_ = l_Lean_instInhabitedExpr;
v___f_4584_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4584_, 0, v___x_4583_);
lean_closure_set(v___f_4584_, 1, v___x_4581_);
lean_closure_set(v___f_4584_, 2, v_givenNames_4574_);
lean_closure_set(v___f_4584_, 3, v_config_4575_);
v___x_4585_ = lean_unsigned_to_nat(1u);
v___x_4586_ = lean_mk_empty_array_with_capacity(v___x_4585_);
v___x_4587_ = lean_array_push(v___x_4586_, v_fvarId_4573_);
v___x_4588_ = 0;
v___x_4589_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4572_, v___x_4587_, v___f_4584_, v___x_4588_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
return v___x_4589_;
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
lean_dec_ref(v_config_4575_);
lean_dec(v_givenNames_4574_);
lean_dec(v_fvarId_4573_);
lean_dec(v_mvarId_4572_);
v_a_4590_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4582_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4582_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4598_, lean_object* v_fvarId_4599_, lean_object* v_givenNames_4600_, lean_object* v_config_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4598_, v_fvarId_4599_, v_givenNames_4600_, v_config_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4608_, lean_object* v___x_4609_, lean_object* v_config_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v___x_4616_; 
lean_inc(v___x_4609_);
lean_inc(v_mvarId_4608_);
v___x_4616_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4608_, v___x_4609_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v___x_4617_; 
lean_dec_ref(v___x_4616_);
lean_inc(v_mvarId_4608_);
v___x_4617_ = l_Lean_MVarId_getType(v_mvarId_4608_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4619_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_a_4618_);
lean_dec_ref(v___x_4617_);
lean_inc(v_a_4618_);
v___x_4619_ = l_Lean_Meta_liftLets(v_a_4618_, v_config_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; uint8_t v___x_4621_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref(v___x_4619_);
v___x_4621_ = lean_expr_eqv(v_a_4618_, v_a_4620_);
lean_dec(v_a_4618_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; 
lean_dec(v___x_4609_);
v___x_4622_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4608_, v_a_4620_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; 
lean_inc(v_mvarId_4608_);
v___x_4623_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4609_, v_mvarId_4608_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v___x_4624_; 
lean_dec_ref(v___x_4623_);
v___x_4624_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4608_, v_a_4620_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
return v___x_4624_;
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_dec(v_a_4620_);
lean_dec(v_mvarId_4608_);
v_a_4625_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4623_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4623_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
lean_dec(v_a_4618_);
lean_dec(v___x_4609_);
lean_dec(v_mvarId_4608_);
v_a_4633_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4619_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4619_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec_ref(v_config_4610_);
lean_dec(v___x_4609_);
lean_dec(v_mvarId_4608_);
v_a_4641_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4617_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4617_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
lean_dec_ref(v_config_4610_);
lean_dec(v___x_4609_);
lean_dec(v_mvarId_4608_);
v_a_4649_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4616_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4616_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4657_, lean_object* v___x_4658_, lean_object* v_config_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4657_, v___x_4658_, v_config_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4669_, lean_object* v_config_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v___x_4676_; lean_object* v___f_4677_; lean_object* v___x_4678_; 
v___x_4676_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4669_);
v___f_4677_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4677_, 0, v_mvarId_4669_);
lean_closure_set(v___f_4677_, 1, v___x_4676_);
lean_closure_set(v___f_4677_, 2, v_config_4670_);
v___x_4678_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4669_, v___f_4677_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4679_, lean_object* v_config_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l_Lean_MVarId_liftLets(v_mvarId_4679_, v_config_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4687_, lean_object* v_fvars_4688_, lean_object* v_targetNew_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4687_, v_targetNew_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4709_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4698_ = v___x_4695_;
v_isShared_4699_ = v_isSharedCheck_4709_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4695_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4709_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4700_; size_t v_sz_4701_; size_t v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4707_; 
v___x_4700_ = lean_box(0);
v_sz_4701_ = lean_array_size(v_fvars_4688_);
v___x_4702_ = ((size_t)0ULL);
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4701_, v___x_4702_, v_fvars_4688_);
v___x_4704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
lean_ctor_set(v___x_4704_, 1, v_a_4696_);
v___x_4705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4700_);
lean_ctor_set(v___x_4705_, 1, v___x_4704_);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 0, v___x_4705_);
v___x_4707_ = v___x_4698_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_dec_ref(v_fvars_4688_);
v_a_4710_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4695_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4695_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4718_, lean_object* v_fvars_4719_, lean_object* v_targetNew_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4718_, v_fvars_4719_, v_targetNew_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4727_, lean_object* v_config_4728_, lean_object* v___f_4729_, lean_object* v___x_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v___x_4736_; 
lean_inc(v_mvarId_4727_);
v___x_4736_ = l_Lean_MVarId_getType(v_mvarId_4727_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref(v___x_4736_);
switch(lean_obj_tag(v_a_4737_))
{
case 7:
{
lean_object* v_binderName_4738_; lean_object* v_binderType_4739_; lean_object* v_body_4740_; uint8_t v_binderInfo_4741_; lean_object* v___x_4742_; 
v_binderName_4738_ = lean_ctor_get(v_a_4737_, 0);
lean_inc(v_binderName_4738_);
v_binderType_4739_ = lean_ctor_get(v_a_4737_, 1);
lean_inc_ref(v_binderType_4739_);
v_body_4740_ = lean_ctor_get(v_a_4737_, 2);
lean_inc_ref(v_body_4740_);
v_binderInfo_4741_ = lean_ctor_get_uint8(v_a_4737_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4737_);
lean_inc_ref(v_binderType_4739_);
v___x_4742_ = l_Lean_Meta_liftLets(v_binderType_4739_, v_config_4728_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; uint8_t v___x_4751_; 
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc(v_a_4743_);
lean_dec_ref(v___x_4742_);
v___x_4751_ = lean_expr_eqv(v_binderType_4739_, v_a_4743_);
lean_dec_ref(v_binderType_4739_);
if (v___x_4751_ == 0)
{
lean_dec(v___x_4730_);
lean_dec(v_mvarId_4727_);
v___y_4745_ = v___y_4731_;
v___y_4746_ = v___y_4732_;
v___y_4747_ = v___y_4733_;
v___y_4748_ = v___y_4734_;
goto v___jp_4744_;
}
else
{
lean_object* v___x_4752_; 
v___x_4752_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4730_, v_mvarId_4727_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_dec_ref(v___x_4752_);
v___y_4745_ = v___y_4731_;
v___y_4746_ = v___y_4732_;
v___y_4747_ = v___y_4733_;
v___y_4748_ = v___y_4734_;
goto v___jp_4744_;
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec(v_a_4743_);
lean_dec_ref(v_body_4740_);
lean_dec(v_binderName_4738_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec_ref(v___f_4729_);
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4752_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4752_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
v___jp_4744_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = l_Lean_Expr_forallE___override(v_binderName_4738_, v_a_4743_, v_body_4740_, v_binderInfo_4741_);
v___x_4750_ = lean_apply_6(v___f_4729_, v___x_4749_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, lean_box(0));
return v___x_4750_;
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v_body_4740_);
lean_dec_ref(v_binderType_4739_);
lean_dec(v_binderName_4738_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___x_4730_);
lean_dec_ref(v___f_4729_);
lean_dec(v_mvarId_4727_);
v_a_4761_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4742_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4742_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
case 8:
{
lean_object* v_declName_4769_; lean_object* v_type_4770_; lean_object* v_value_4771_; lean_object* v_body_4772_; uint8_t v_nondep_4773_; lean_object* v___x_4774_; 
v_declName_4769_ = lean_ctor_get(v_a_4737_, 0);
lean_inc(v_declName_4769_);
v_type_4770_ = lean_ctor_get(v_a_4737_, 1);
lean_inc_ref(v_type_4770_);
v_value_4771_ = lean_ctor_get(v_a_4737_, 2);
lean_inc_ref(v_value_4771_);
v_body_4772_ = lean_ctor_get(v_a_4737_, 3);
lean_inc_ref(v_body_4772_);
v_nondep_4773_ = lean_ctor_get_uint8(v_a_4737_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4737_);
lean_inc_ref(v_config_4728_);
lean_inc_ref(v_type_4770_);
v___x_4774_ = l_Lean_Meta_liftLets(v_type_4770_, v_config_4728_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v_a_4775_; lean_object* v___x_4776_; 
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc(v_a_4775_);
lean_dec_ref(v___x_4774_);
lean_inc_ref(v_value_4771_);
v___x_4776_ = l_Lean_Meta_liftLets(v_value_4771_, v_config_4728_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___y_4779_; lean_object* v___y_4780_; lean_object* v___y_4781_; lean_object* v___y_4782_; uint8_t v___y_4786_; uint8_t v___x_4796_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref(v___x_4776_);
v___x_4796_ = lean_expr_eqv(v_type_4770_, v_a_4775_);
lean_dec_ref(v_type_4770_);
if (v___x_4796_ == 0)
{
lean_dec_ref(v_value_4771_);
v___y_4786_ = v___x_4796_;
goto v___jp_4785_;
}
else
{
uint8_t v___x_4797_; 
v___x_4797_ = lean_expr_eqv(v_value_4771_, v_a_4777_);
lean_dec_ref(v_value_4771_);
v___y_4786_ = v___x_4797_;
goto v___jp_4785_;
}
v___jp_4778_:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4783_ = l_Lean_Expr_letE___override(v_declName_4769_, v_a_4775_, v_a_4777_, v_body_4772_, v_nondep_4773_);
v___x_4784_ = lean_apply_6(v___f_4729_, v___x_4783_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, lean_box(0));
return v___x_4784_;
}
v___jp_4785_:
{
if (v___y_4786_ == 0)
{
lean_dec(v___x_4730_);
lean_dec(v_mvarId_4727_);
v___y_4779_ = v___y_4731_;
v___y_4780_ = v___y_4732_;
v___y_4781_ = v___y_4733_;
v___y_4782_ = v___y_4734_;
goto v___jp_4778_;
}
else
{
lean_object* v___x_4787_; 
v___x_4787_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4730_, v_mvarId_4727_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_dec_ref(v___x_4787_);
v___y_4779_ = v___y_4731_;
v___y_4780_ = v___y_4732_;
v___y_4781_ = v___y_4733_;
v___y_4782_ = v___y_4734_;
goto v___jp_4778_;
}
else
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4795_; 
lean_dec(v_a_4777_);
lean_dec(v_a_4775_);
lean_dec_ref(v_body_4772_);
lean_dec(v_declName_4769_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec_ref(v___f_4729_);
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4790_ = v___x_4787_;
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4787_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4793_; 
if (v_isShared_4791_ == 0)
{
v___x_4793_ = v___x_4790_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4788_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec(v_a_4775_);
lean_dec_ref(v_body_4772_);
lean_dec_ref(v_value_4771_);
lean_dec_ref(v_type_4770_);
lean_dec(v_declName_4769_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___x_4730_);
lean_dec_ref(v___f_4729_);
lean_dec(v_mvarId_4727_);
v_a_4798_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4776_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4776_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
lean_dec_ref(v_body_4772_);
lean_dec_ref(v_value_4771_);
lean_dec_ref(v_type_4770_);
lean_dec(v_declName_4769_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___x_4730_);
lean_dec_ref(v___f_4729_);
lean_dec_ref(v_config_4728_);
lean_dec(v_mvarId_4727_);
v_a_4806_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4774_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4774_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
default: 
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec(v_a_4737_);
lean_dec_ref(v___f_4729_);
lean_dec_ref(v_config_4728_);
v___x_4814_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4815_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4730_, v_mvarId_4727_, v___x_4814_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
return v___x_4815_;
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___x_4730_);
lean_dec_ref(v___f_4729_);
lean_dec_ref(v_config_4728_);
lean_dec(v_mvarId_4727_);
v_a_4816_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4736_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4736_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4824_, lean_object* v_config_4825_, lean_object* v___f_4826_, lean_object* v___x_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4824_, v_config_4825_, v___f_4826_, v___x_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4834_, lean_object* v___x_4835_, lean_object* v_mvarId_4836_, lean_object* v_fvars_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v___f_4843_; lean_object* v___f_4844_; lean_object* v___x_4845_; 
lean_inc(v_mvarId_4836_);
v___f_4843_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4843_, 0, v_mvarId_4836_);
lean_closure_set(v___f_4843_, 1, v_fvars_4837_);
lean_inc(v_mvarId_4836_);
v___f_4844_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4844_, 0, v_mvarId_4836_);
lean_closure_set(v___f_4844_, 1, v_config_4834_);
lean_closure_set(v___f_4844_, 2, v___f_4843_);
lean_closure_set(v___f_4844_, 3, v___x_4835_);
v___x_4845_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4836_, v___f_4844_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4846_, lean_object* v___x_4847_, lean_object* v_mvarId_4848_, lean_object* v_fvars_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4846_, v___x_4847_, v_mvarId_4848_, v_fvars_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4856_, lean_object* v_fvarId_4857_, lean_object* v_config_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4856_);
v___x_4865_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4856_, v___x_4864_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v___f_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; uint8_t v___x_4870_; lean_object* v___x_4871_; 
lean_dec_ref(v___x_4865_);
v___f_4866_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4866_, 0, v_config_4858_);
lean_closure_set(v___f_4866_, 1, v___x_4864_);
v___x_4867_ = lean_unsigned_to_nat(1u);
v___x_4868_ = lean_mk_empty_array_with_capacity(v___x_4867_);
v___x_4869_ = lean_array_push(v___x_4868_, v_fvarId_4857_);
v___x_4870_ = 0;
v___x_4871_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4856_, v___x_4869_, v___f_4866_, v___x_4870_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4880_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4874_ = v___x_4871_;
v_isShared_4875_ = v_isSharedCheck_4880_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4871_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4880_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v_snd_4876_; lean_object* v___x_4878_; 
v_snd_4876_ = lean_ctor_get(v_a_4872_, 1);
lean_inc(v_snd_4876_);
lean_dec(v_a_4872_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 0, v_snd_4876_);
v___x_4878_ = v___x_4874_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_snd_4876_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
v_a_4881_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4871_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4871_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
lean_dec_ref(v_config_4858_);
lean_dec(v_fvarId_4857_);
lean_dec(v_mvarId_4856_);
v_a_4889_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4865_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4865_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4897_, lean_object* v_fvarId_4898_, lean_object* v_config_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4897_, v_fvarId_4898_, v_config_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
lean_dec_ref(v_a_4900_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4906_, lean_object* v___x_4907_, uint8_t v_failIfUnchanged_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; 
lean_inc(v___x_4907_);
lean_inc(v_mvarId_4906_);
v___x_4914_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4906_, v___x_4907_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v___x_4915_; 
lean_dec_ref(v___x_4914_);
lean_inc(v_mvarId_4906_);
v___x_4915_ = l_Lean_MVarId_getType(v_mvarId_4906_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref(v___x_4915_);
lean_inc(v_a_4916_);
v___x_4917_ = l_Lean_Meta_letToHave(v_a_4916_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
if (lean_obj_tag(v___x_4917_) == 0)
{
if (v_failIfUnchanged_4908_ == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4919_; 
lean_dec(v_a_4916_);
lean_dec(v___x_4907_);
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref(v___x_4917_);
v___x_4919_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4906_, v_a_4918_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
return v___x_4919_;
}
else
{
lean_object* v_a_4920_; uint8_t v___x_4921_; 
v_a_4920_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4920_);
lean_dec_ref(v___x_4917_);
v___x_4921_ = lean_expr_eqv(v_a_4916_, v_a_4920_);
lean_dec(v_a_4916_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; 
lean_dec(v___x_4907_);
v___x_4922_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4906_, v_a_4920_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
return v___x_4922_;
}
else
{
lean_object* v___x_4923_; 
lean_inc(v_mvarId_4906_);
v___x_4923_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4907_, v_mvarId_4906_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v___x_4924_; 
lean_dec_ref(v___x_4923_);
v___x_4924_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4906_, v_a_4920_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
return v___x_4924_;
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec(v_a_4920_);
lean_dec(v_mvarId_4906_);
v_a_4925_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4923_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4923_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4940_; 
lean_dec(v_a_4916_);
lean_dec(v___x_4907_);
lean_dec(v_mvarId_4906_);
v_a_4933_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4935_ = v___x_4917_;
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4917_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4938_; 
if (v_isShared_4936_ == 0)
{
v___x_4938_ = v___x_4935_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v___x_4907_);
lean_dec(v_mvarId_4906_);
v_a_4941_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4915_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4915_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec(v___x_4907_);
lean_dec(v_mvarId_4906_);
v_a_4949_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4914_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4914_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4957_, lean_object* v___x_4958_, lean_object* v_failIfUnchanged_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4965_; lean_object* v_res_4966_; 
v_failIfUnchanged_boxed_4965_ = lean_unbox(v_failIfUnchanged_4959_);
v_res_4966_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4957_, v___x_4958_, v_failIfUnchanged_boxed_4965_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4970_, uint8_t v_failIfUnchanged_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___f_4979_; lean_object* v___x_4980_; 
v___x_4977_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4978_ = lean_box(v_failIfUnchanged_4971_);
lean_inc(v_mvarId_4970_);
v___f_4979_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4979_, 0, v_mvarId_4970_);
lean_closure_set(v___f_4979_, 1, v___x_4977_);
lean_closure_set(v___f_4979_, 2, v___x_4978_);
v___x_4980_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4970_, v___f_4979_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4981_, lean_object* v_failIfUnchanged_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4988_; lean_object* v_res_4989_; 
v_failIfUnchanged_boxed_4988_ = lean_unbox(v_failIfUnchanged_4982_);
v_res_4989_ = l_Lean_MVarId_letToHave(v_mvarId_4981_, v_failIfUnchanged_boxed_4988_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
lean_dec(v_a_4986_);
lean_dec_ref(v_a_4985_);
lean_dec(v_a_4984_);
lean_dec_ref(v_a_4983_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4990_, lean_object* v___x_4991_, lean_object* v_fvarId_4992_, uint8_t v_failIfUnchanged_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v___x_4999_; 
lean_inc(v___x_4991_);
lean_inc(v_mvarId_4990_);
v___x_4999_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4990_, v___x_4991_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v___x_5000_; 
lean_dec_ref(v___x_4999_);
lean_inc(v_fvarId_4992_);
v___x_5000_ = l_Lean_FVarId_getType___redArg(v_fvarId_4992_, v___y_4994_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; lean_object* v___x_5002_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
lean_inc(v_a_5001_);
lean_dec_ref(v___x_5000_);
lean_inc(v_a_5001_);
v___x_5002_ = l_Lean_Meta_letToHave(v_a_5001_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_5002_) == 0)
{
if (v_failIfUnchanged_4993_ == 0)
{
lean_object* v_a_5003_; lean_object* v___x_5004_; 
lean_dec(v_a_5001_);
lean_dec(v___x_4991_);
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
lean_inc(v_a_5003_);
lean_dec_ref(v___x_5002_);
v___x_5004_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4990_, v_fvarId_4992_, v_a_5003_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
return v___x_5004_;
}
else
{
lean_object* v_a_5005_; uint8_t v___x_5006_; 
v_a_5005_ = lean_ctor_get(v___x_5002_, 0);
lean_inc(v_a_5005_);
lean_dec_ref(v___x_5002_);
v___x_5006_ = lean_expr_eqv(v_a_5001_, v_a_5005_);
lean_dec(v_a_5001_);
if (v___x_5006_ == 0)
{
lean_object* v___x_5007_; 
lean_dec(v___x_4991_);
v___x_5007_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4990_, v_fvarId_4992_, v_a_5005_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
return v___x_5007_;
}
else
{
lean_object* v___x_5008_; 
lean_inc(v_mvarId_4990_);
v___x_5008_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4991_, v_mvarId_4990_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v___x_5009_; 
lean_dec_ref(v___x_5008_);
v___x_5009_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4990_, v_fvarId_4992_, v_a_5005_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
return v___x_5009_;
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
lean_dec(v_a_5005_);
lean_dec(v_fvarId_4992_);
lean_dec(v_mvarId_4990_);
v_a_5010_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_5008_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_5008_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec(v_a_5001_);
lean_dec(v_fvarId_4992_);
lean_dec(v___x_4991_);
lean_dec(v_mvarId_4990_);
v_a_5018_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5002_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5002_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
lean_dec(v_fvarId_4992_);
lean_dec(v___x_4991_);
lean_dec(v_mvarId_4990_);
v_a_5026_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_5000_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5000_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec(v_fvarId_4992_);
lean_dec(v___x_4991_);
lean_dec(v_mvarId_4990_);
v_a_5034_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_4999_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_4999_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5042_, lean_object* v___x_5043_, lean_object* v_fvarId_5044_, lean_object* v_failIfUnchanged_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5051_; lean_object* v_res_5052_; 
v_failIfUnchanged_boxed_5051_ = lean_unbox(v_failIfUnchanged_5045_);
v_res_5052_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5042_, v___x_5043_, v_fvarId_5044_, v_failIfUnchanged_boxed_5051_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5053_, lean_object* v_fvarId_5054_, uint8_t v_failIfUnchanged_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___f_5063_; lean_object* v___x_5064_; 
v___x_5061_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5062_ = lean_box(v_failIfUnchanged_5055_);
lean_inc(v_mvarId_5053_);
v___f_5063_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5063_, 0, v_mvarId_5053_);
lean_closure_set(v___f_5063_, 1, v___x_5061_);
lean_closure_set(v___f_5063_, 2, v_fvarId_5054_);
lean_closure_set(v___f_5063_, 3, v___x_5062_);
v___x_5064_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5053_, v___f_5063_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5065_, lean_object* v_fvarId_5066_, lean_object* v_failIfUnchanged_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5073_; lean_object* v_res_5074_; 
v_failIfUnchanged_boxed_5073_ = lean_unbox(v_failIfUnchanged_5067_);
v_res_5074_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5065_, v_fvarId_5066_, v_failIfUnchanged_boxed_5073_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
return v_res_5074_;
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
