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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object* v_fvar_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_decls_665_; lean_object* v_fvarSet_666_; lean_object* v_fvarSet_667_; lean_object* v___x_668_; lean_object* v___x_669_; size_t v_sz_670_; size_t v___x_671_; lean_object* v___x_672_; 
v___x_664_ = lean_st_ref_get(v_a_658_);
v_decls_665_ = lean_ctor_get(v___x_664_, 1);
lean_inc_ref(v_decls_665_);
lean_dec(v___x_664_);
v_fvarSet_666_ = lean_box(1);
v_fvarSet_667_ = l_Lean_FVarIdSet_insert(v_fvarSet_666_, v_fvar_655_);
v___x_668_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_fvarSet_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v_sz_670_ = lean_array_size(v_decls_665_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_decls_665_, v_sz_670_, v___x_671_, v___x_669_);
lean_dec_ref(v_decls_665_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_695_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_695_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_695_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_695_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v_snd_678_; lean_object* v_fst_679_; lean_object* v_snd_680_; lean_object* v_givenNames_681_; lean_object* v_valueMap_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_693_; 
v___x_677_ = lean_st_ref_take(v_a_658_);
v_snd_678_ = lean_ctor_get(v_a_673_, 1);
lean_inc(v_snd_678_);
lean_dec(v_a_673_);
v_fst_679_ = lean_ctor_get(v_snd_678_, 0);
lean_inc(v_fst_679_);
v_snd_680_ = lean_ctor_get(v_snd_678_, 1);
lean_inc(v_snd_680_);
lean_dec(v_snd_678_);
v_givenNames_681_ = lean_ctor_get(v___x_677_, 0);
v_valueMap_682_ = lean_ctor_get(v___x_677_, 2);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v___x_677_, 1);
lean_dec(v_unused_694_);
v___x_684_ = v___x_677_;
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_valueMap_682_);
lean_inc(v_givenNames_681_);
lean_dec(v___x_677_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_fst_679_);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_givenNames_681_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_fst_679_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_valueMap_682_);
v___x_687_ = v_reuseFailAlloc_692_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_st_ref_set(v_a_658_, v___x_687_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v_snd_680_);
v___x_690_ = v___x_675_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_snd_680_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_672_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_672_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object* v_fvar_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_ExtractLets_flushDecls(v_fvar_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
return v_res_713_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object* v_00_u03b2_714_, lean_object* v_k_715_, lean_object* v_t_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_715_, v_t_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object* v_00_u03b2_718_, lean_object* v_k_719_, lean_object* v_t_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(v_00_u03b2_718_, v_k_719_, v_t_720_);
lean_dec(v_t_720_);
lean_dec(v_k_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object* v_as_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_723_, v_sz_724_, v_i_725_, v_b_726_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object* v_as_736_, lean_object* v_sz_737_, lean_object* v_i_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
size_t v_sz_boxed_748_; size_t v_i_boxed_749_; lean_object* v_res_750_; 
v_sz_boxed_748_ = lean_unbox_usize(v_sz_737_);
lean_dec(v_sz_737_);
v_i_boxed_749_ = lean_unbox_usize(v_i_738_);
lean_dec(v_i_738_);
v_res_750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_736_, v_sz_boxed_748_, v_i_boxed_749_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec_ref(v_as_736_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object* v_x_751_){
_start:
{
lean_object* v_decl_752_; 
v_decl_752_ = lean_ctor_get(v_x_751_, 0);
lean_inc_ref(v_decl_752_);
return v_decl_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object* v_x_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(v_x_753_);
lean_dec_ref(v_x_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object* v_lctx_755_, lean_object* v_x1_756_, lean_object* v_x2_757_){
_start:
{
lean_object* v_decl_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_decl_758_ = lean_ctor_get(v_x2_757_, 0);
v___x_759_ = l_Lean_LocalDecl_fvarId(v_decl_758_);
v___x_760_ = l_Lean_LocalContext_contains(v_lctx_755_, v___x_759_);
lean_dec(v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_array_push(v_x1_756_, v_x2_757_);
return v___x_761_;
}
else
{
lean_dec_ref(v_x2_757_);
return v_x1_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object* v_lctx_762_, lean_object* v_x1_763_, lean_object* v_x2_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(v_lctx_762_, v_x1_763_, v_x2_764_);
lean_dec_ref(v_lctx_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_k_788_, lean_object* v_decls_789_, lean_object* v_lctx_790_){
_start:
{
lean_object* v___y_792_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_array_get_size(v_decls_789_);
v___x_801_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_802_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_803_ = lean_nat_dec_lt(v___x_799_, v___x_800_);
if (v___x_803_ == 0)
{
lean_dec_ref(v_lctx_790_);
lean_dec_ref(v_decls_789_);
v___y_792_ = v___x_801_;
goto v___jp_791_;
}
else
{
lean_object* v___f_804_; uint8_t v___x_805_; 
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_804_, 0, v_lctx_790_);
v___x_805_ = lean_nat_dec_le(v___x_800_, v___x_800_);
if (v___x_805_ == 0)
{
if (v___x_803_ == 0)
{
lean_dec_ref(v___f_804_);
lean_dec_ref(v_decls_789_);
v___y_792_ = v___x_801_;
goto v___jp_791_;
}
else
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((size_t)0ULL);
v___x_807_ = lean_usize_of_nat(v___x_800_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_802_, v___f_804_, v_decls_789_, v___x_806_, v___x_807_, v___x_801_);
v___y_792_ = v___x_808_;
goto v___jp_791_;
}
}
else
{
size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((size_t)0ULL);
v___x_810_ = lean_usize_of_nat(v___x_800_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_802_, v___f_804_, v_decls_789_, v___x_809_, v___x_810_, v___x_801_);
v___y_792_ = v___x_811_;
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v___x_793_; size_t v_sz_794_; size_t v___x_795_; lean_object* v_decls_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_793_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_794_ = lean_array_size(v___y_792_);
v___x_795_ = ((size_t)0ULL);
v_decls_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_793_, v___f_785_, v_sz_794_, v___x_795_, v___y_792_);
v___x_797_ = lean_array_to_list(v_decls_796_);
v___x_798_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_786_, v_inst_787_, v___x_797_, v_k_788_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_decls_816_, lean_object* v_k_817_){
_start:
{
lean_object* v_toBind_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___x_821_; 
v_toBind_818_ = lean_ctor_get(v_inst_813_, 1);
lean_inc(v_toBind_818_);
v___f_819_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_820_, 0, v___f_819_);
lean_closure_set(v___f_820_, 1, v_inst_814_);
lean_closure_set(v___f_820_, 2, v_inst_813_);
lean_closure_set(v___f_820_, 3, v_k_817_);
lean_closure_set(v___f_820_, 4, v_decls_816_);
v___x_821_ = lean_apply_4(v_toBind_818_, lean_box(0), lean_box(0), v_inst_815_, v___f_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_822_, lean_object* v_00_u03b1_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_decls_827_, lean_object* v_k_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_824_, v_inst_825_, v_inst_826_, v_decls_827_, v_k_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_830_, size_t v_i_831_, size_t v_stop_832_, lean_object* v_b_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_eq(v_i_831_, v_stop_832_);
if (v___x_834_ == 0)
{
size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v_decl_838_; uint8_t v_isLet_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_sub(v_i_831_, v___x_835_);
v___x_837_ = lean_array_uget_borrowed(v_as_830_, v___x_836_);
v_decl_838_ = lean_ctor_get(v___x_837_, 0);
v_isLet_839_ = lean_ctor_get_uint8(v___x_837_, sizeof(void*)*1);
v___x_840_ = l_Lean_LocalDecl_userName(v_decl_838_);
v___x_841_ = l_Lean_LocalDecl_type(v_decl_838_);
v___x_842_ = l_Lean_LocalDecl_value(v_decl_838_, v___x_834_);
lean_inc_ref(v_decl_838_);
v___x_843_ = l_Lean_LocalDecl_toExpr(v_decl_838_);
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_mk_empty_array_with_capacity(v___x_844_);
v___x_846_ = lean_array_push(v___x_845_, v___x_843_);
v___x_847_ = lean_expr_abstract(v_b_833_, v___x_846_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v_b_833_);
if (v_isLet_839_ == 0)
{
uint8_t v___x_848_; lean_object* v___x_849_; 
v___x_848_ = 1;
v___x_849_ = l_Lean_Expr_letE___override(v___x_840_, v___x_841_, v___x_842_, v___x_847_, v___x_848_);
v_i_831_ = v___x_836_;
v_b_833_ = v___x_849_;
goto _start;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Expr_letE___override(v___x_840_, v___x_841_, v___x_842_, v___x_847_, v___x_834_);
v_i_831_ = v___x_836_;
v_b_833_ = v___x_851_;
goto _start;
}
}
else
{
return v_b_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object* v_as_853_, lean_object* v_i_854_, lean_object* v_stop_855_, lean_object* v_b_856_){
_start:
{
size_t v_i_boxed_857_; size_t v_stop_boxed_858_; lean_object* v_res_859_; 
v_i_boxed_857_ = lean_unbox_usize(v_i_854_);
lean_dec(v_i_854_);
v_stop_boxed_858_ = lean_unbox_usize(v_stop_855_);
lean_dec(v_stop_855_);
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_853_, v_i_boxed_857_, v_stop_boxed_858_, v_b_856_);
lean_dec_ref(v_as_853_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object* v_decls_860_, lean_object* v_e_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_862_ = lean_array_get_size(v_decls_860_);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_nat_dec_lt(v___x_863_, v___x_862_);
if (v___x_864_ == 0)
{
return v_e_861_;
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_usize_of_nat(v___x_862_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_860_, v___x_865_, v___x_866_, v_e_861_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object* v_decls_868_, lean_object* v_e_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_868_, v_e_869_);
lean_dec_ref(v_decls_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object* v_fvarId_871_, size_t v_sz_872_, size_t v_i_873_, lean_object* v_bs_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = lean_usize_dec_lt(v_i_873_, v_sz_872_);
if (v___x_875_ == 0)
{
return v_bs_874_;
}
else
{
lean_object* v_v_876_; lean_object* v_decl_877_; lean_object* v___x_878_; lean_object* v_bs_x27_879_; lean_object* v___y_881_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_v_876_ = lean_array_uget(v_bs_874_, v_i_873_);
v_decl_877_ = lean_ctor_get(v_v_876_, 0);
v___x_878_ = lean_unsigned_to_nat(0u);
v_bs_x27_879_ = lean_array_uset(v_bs_874_, v_i_873_, v___x_878_);
v___x_886_ = l_Lean_LocalDecl_fvarId(v_decl_877_);
v___x_887_ = l_Lean_instBEqFVarId_beq(v___x_886_, v_fvarId_871_);
lean_dec(v___x_886_);
if (v___x_887_ == 0)
{
v___y_881_ = v_v_876_;
goto v___jp_880_;
}
else
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_inc_ref(v_decl_877_);
v_isSharedCheck_894_ = !lean_is_exclusive(v_v_876_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_v_876_, 0);
lean_dec(v_unused_895_);
v___x_889_ = v_v_876_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_v_876_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_decl_877_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*1, v___x_887_);
v___y_881_ = v___x_892_;
goto v___jp_880_;
}
}
}
v___jp_880_:
{
size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_add(v_i_873_, v___x_882_);
v___x_884_ = lean_array_uset(v_bs_x27_879_, v_i_873_, v___y_881_);
v_i_873_ = v___x_883_;
v_bs_874_ = v___x_884_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object* v_fvarId_896_, lean_object* v_sz_897_, lean_object* v_i_898_, lean_object* v_bs_899_){
_start:
{
size_t v_sz_boxed_900_; size_t v_i_boxed_901_; lean_object* v_res_902_; 
v_sz_boxed_900_ = lean_unbox_usize(v_sz_897_);
lean_dec(v_sz_897_);
v_i_boxed_901_ = lean_unbox_usize(v_i_898_);
lean_dec(v_i_898_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_896_, v_sz_boxed_900_, v_i_boxed_901_, v_bs_899_);
lean_dec(v_fvarId_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object* v_fvarId_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; lean_object* v_givenNames_907_; lean_object* v_decls_908_; lean_object* v_valueMap_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_922_; 
v___x_906_ = lean_st_ref_take(v_a_904_);
v_givenNames_907_ = lean_ctor_get(v___x_906_, 0);
v_decls_908_ = lean_ctor_get(v___x_906_, 1);
v_valueMap_909_ = lean_ctor_get(v___x_906_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_922_ == 0)
{
v___x_911_ = v___x_906_;
v_isShared_912_ = v_isSharedCheck_922_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_valueMap_909_);
lean_inc(v_decls_908_);
lean_inc(v_givenNames_907_);
lean_dec(v___x_906_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_922_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
size_t v_sz_913_; size_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v_sz_913_ = lean_array_size(v_decls_908_);
v___x_914_ = ((size_t)0ULL);
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_903_, v_sz_913_, v___x_914_, v_decls_908_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_915_);
v___x_917_ = v___x_911_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_givenNames_907_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_valueMap_909_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_st_ref_set(v_a_904_, v___x_917_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object* v_fvarId_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec(v_fvarId_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object* v_fvarId_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_927_, v_a_930_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object* v_fvarId_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_fvarId_937_);
return v_res_946_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0(lean_object* v_fvarId_947_, lean_object* v_x_948_){
_start:
{
lean_object* v_decl_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_decl_949_ = lean_ctor_get(v_x_948_, 0);
v___x_950_ = l_Lean_LocalDecl_fvarId(v_decl_949_);
v___x_951_ = l_Lean_instBEqFVarId_beq(v___x_950_, v_fvarId_947_);
lean_dec(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0___boxed(lean_object* v_fvarId_952_, lean_object* v_x_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0(v_fvarId_952_, v_x_953_);
lean_dec_ref(v_x_953_);
lean_dec(v_fvarId_952_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(lean_object* v___x_956_, lean_object* v_as_957_, size_t v_i_958_, size_t v_stop_959_, lean_object* v_b_960_){
_start:
{
lean_object* v___y_962_; uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_eq(v_i_958_, v_stop_959_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v_decl_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_967_ = lean_array_uget_borrowed(v_as_957_, v_i_958_);
v_decl_968_ = lean_ctor_get(v___x_967_, 0);
v___x_969_ = l_Lean_LocalDecl_fvarId(v_decl_968_);
v___x_970_ = l_Lean_LocalContext_contains(v___x_956_, v___x_969_);
lean_dec(v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_inc(v___x_967_);
v___x_971_ = lean_array_push(v_b_960_, v___x_967_);
v___y_962_ = v___x_971_;
goto v___jp_961_;
}
else
{
v___y_962_ = v_b_960_;
goto v___jp_961_;
}
}
else
{
return v_b_960_;
}
v___jp_961_:
{
size_t v___x_963_; size_t v___x_964_; 
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_958_, v___x_963_);
v_i_958_ = v___x_964_;
v_b_960_ = v___y_962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2___boxed(lean_object* v___x_972_, lean_object* v_as_973_, lean_object* v_i_974_, lean_object* v_stop_975_, lean_object* v_b_976_){
_start:
{
size_t v_i_boxed_977_; size_t v_stop_boxed_978_; lean_object* v_res_979_; 
v_i_boxed_977_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_stop_boxed_978_ = lean_unbox_usize(v_stop_975_);
lean_dec(v_stop_975_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v___x_972_, v_as_973_, v_i_boxed_977_, v_stop_boxed_978_, v_b_976_);
lean_dec_ref(v_as_973_);
lean_dec_ref(v___x_972_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
lean_inc(v___y_983_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
v___x_989_ = lean_apply_8(v_x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, lean_box(0));
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(v_x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(lean_object* v_decls_1000_, lean_object* v_x_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___f_1010_; lean_object* v___x_1011_; 
lean_inc(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc_ref(v___y_1002_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1010_, 0, v_x_1001_);
lean_closure_set(v___f_1010_, 1, v___y_1002_);
lean_closure_set(v___f_1010_, 2, v___y_1003_);
lean_closure_set(v___f_1010_, 3, v___y_1004_);
v___x_1011_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1000_, v___f_1010_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1011_) == 0)
{
return v___x_1011_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___boxed(lean_object* v_decls_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v_decls_1020_, v_x_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(size_t v_sz_1031_, size_t v_i_1032_, lean_object* v_bs_1033_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_usize_dec_lt(v_i_1032_, v_sz_1031_);
if (v___x_1034_ == 0)
{
return v_bs_1033_;
}
else
{
lean_object* v_v_1035_; lean_object* v_decl_1036_; lean_object* v___x_1037_; lean_object* v_bs_x27_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v_v_1035_ = lean_array_uget_borrowed(v_bs_1033_, v_i_1032_);
v_decl_1036_ = lean_ctor_get(v_v_1035_, 0);
lean_inc_ref(v_decl_1036_);
v___x_1037_ = lean_unsigned_to_nat(0u);
v_bs_x27_1038_ = lean_array_uset(v_bs_1033_, v_i_1032_, v___x_1037_);
v___x_1039_ = ((size_t)1ULL);
v___x_1040_ = lean_usize_add(v_i_1032_, v___x_1039_);
v___x_1041_ = lean_array_uset(v_bs_x27_1038_, v_i_1032_, v_decl_1036_);
v_i_1032_ = v___x_1040_;
v_bs_1033_ = v___x_1041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0___boxed(lean_object* v_sz_1043_, lean_object* v_i_1044_, lean_object* v_bs_1045_){
_start:
{
size_t v_sz_boxed_1046_; size_t v_i_boxed_1047_; lean_object* v_res_1048_; 
v_sz_boxed_1046_ = lean_unbox_usize(v_sz_1043_);
lean_dec(v_sz_1043_);
v_i_boxed_1047_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_boxed_1046_, v_i_boxed_1047_, v_bs_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(lean_object* v_decls_1049_, lean_object* v_k_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___y_1060_; lean_object* v_lctx_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_lctx_1066_ = lean_ctor_get(v___y_1054_, 2);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_array_get_size(v_decls_1049_);
v___x_1069_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_1070_ = lean_nat_dec_lt(v___x_1067_, v___x_1068_);
if (v___x_1070_ == 0)
{
v___y_1060_ = v___x_1069_;
goto v___jp_1059_;
}
else
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_nat_dec_le(v___x_1068_, v___x_1068_);
if (v___x_1071_ == 0)
{
if (v___x_1070_ == 0)
{
v___y_1060_ = v___x_1069_;
goto v___jp_1059_;
}
else
{
size_t v___x_1072_; size_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = ((size_t)0ULL);
v___x_1073_ = lean_usize_of_nat(v___x_1068_);
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v_lctx_1066_, v_decls_1049_, v___x_1072_, v___x_1073_, v___x_1069_);
v___y_1060_ = v___x_1074_;
goto v___jp_1059_;
}
}
else
{
size_t v___x_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = ((size_t)0ULL);
v___x_1076_ = lean_usize_of_nat(v___x_1068_);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__2(v_lctx_1066_, v_decls_1049_, v___x_1075_, v___x_1076_, v___x_1069_);
v___y_1060_ = v___x_1077_;
goto v___jp_1059_;
}
}
v___jp_1059_:
{
size_t v_sz_1061_; size_t v___x_1062_; lean_object* v_decls_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_sz_1061_ = lean_array_size(v___y_1060_);
v___x_1062_ = ((size_t)0ULL);
v_decls_1063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_1061_, v___x_1062_, v___y_1060_);
v___x_1064_ = lean_array_to_list(v_decls_1063_);
v___x_1065_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v___x_1064_, v_k_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg___boxed(lean_object* v_decls_1078_, lean_object* v_k_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1078_, v_k_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec_ref(v_decls_1078_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1089_, lean_object* v_k_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_lctx_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_st_ref_get(v_a_1093_);
v_lctx_1100_ = lean_ctor_get(v_a_1094_, 2);
v___x_1101_ = l_Lean_LocalContext_contains(v_lctx_1100_, v_fvarId_1089_);
if (v___x_1101_ == 0)
{
lean_object* v_decls_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_decls_1102_ = lean_ctor_get(v___x_1099_, 1);
lean_inc_ref(v_decls_1102_);
lean_dec(v___x_1099_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withDeclInContext___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1103_, 0, v_fvarId_1089_);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = l_Array_findIdx_x3f_loop___redArg(v___f_1103_, v_decls_1102_, v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 1)
{
lean_object* v_val_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_val_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1106_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_add(v_val_1106_, v___x_1107_);
lean_dec(v_val_1106_);
v___x_1109_ = l_Array_toSubarray___redArg(v_decls_1102_, v___x_1104_, v___x_1108_);
v___x_1110_ = l_Subarray_copy___redArg(v___x_1109_);
v___x_1111_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v___x_1110_, v_k_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec_ref(v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; 
lean_dec(v___x_1105_);
lean_dec_ref(v_decls_1102_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
lean_inc(v_a_1095_);
lean_inc_ref(v_a_1094_);
lean_inc(v_a_1093_);
lean_inc(v_a_1092_);
lean_inc_ref(v_a_1091_);
v___x_1112_ = lean_apply_8(v_k_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, lean_box(0));
return v___x_1112_;
}
}
else
{
lean_object* v___x_1113_; 
lean_dec(v___x_1099_);
lean_dec(v_fvarId_1089_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
lean_inc(v_a_1095_);
lean_inc_ref(v_a_1094_);
lean_inc(v_a_1093_);
lean_inc(v_a_1092_);
lean_inc_ref(v_a_1091_);
v___x_1113_ = lean_apply_8(v_k_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, lean_box(0));
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1114_, lean_object* v_k_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1114_, v_k_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1125_, lean_object* v_fvarId_1126_, lean_object* v_k_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1126_, v_k_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_fvarId_1138_, lean_object* v_k_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1137_, v_fvarId_1138_, v_k_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1(lean_object* v_00_u03b1_1149_, lean_object* v_decls_1150_, lean_object* v_x_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(v_decls_1150_, v_x_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_decls_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1(v_00_u03b1_1161_, v_decls_1162_, v_x_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_00_u03b1_1173_, lean_object* v_decls_1174_, lean_object* v_k_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1174_, v_k_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_decls_1186_, lean_object* v_k_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_00_u03b1_1185_, v_decls_1186_, v_k_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_decls_1186_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_Expr_hasMVar(v_e_1197_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_e_1197_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; lean_object* v_mctx_1203_; lean_object* v___x_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1207_; lean_object* v_cache_1208_; lean_object* v_zetaDeltaFVarIds_1209_; lean_object* v_postponed_1210_; lean_object* v_diag_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1220_; 
v___x_1202_ = lean_st_ref_get(v___y_1198_);
v_mctx_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_ref(v_mctx_1203_);
lean_dec(v___x_1202_);
v___x_1204_ = l_Lean_instantiateMVarsCore(v_mctx_1203_, v_e_1197_);
v_fst_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_fst_1205_);
v_snd_1206_ = lean_ctor_get(v___x_1204_, 1);
lean_inc(v_snd_1206_);
lean_dec_ref(v___x_1204_);
v___x_1207_ = lean_st_ref_take(v___y_1198_);
v_cache_1208_ = lean_ctor_get(v___x_1207_, 1);
v_zetaDeltaFVarIds_1209_ = lean_ctor_get(v___x_1207_, 2);
v_postponed_1210_ = lean_ctor_get(v___x_1207_, 3);
v_diag_1211_ = lean_ctor_get(v___x_1207_, 4);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1207_, 0);
lean_dec(v_unused_1221_);
v___x_1213_ = v___x_1207_;
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_diag_1211_);
lean_inc(v_postponed_1210_);
lean_inc(v_zetaDeltaFVarIds_1209_);
lean_inc(v_cache_1208_);
lean_dec(v___x_1207_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_snd_1206_);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_snd_1206_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_cache_1208_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_zetaDeltaFVarIds_1209_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_postponed_1210_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_diag_1211_);
v___x_1216_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_st_ref_set(v___y_1198_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_fst_1205_);
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1222_, v___y_1223_);
lean_dec(v___y_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1226_, v___y_1231_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1246_, size_t v_i_1247_, size_t v_stop_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_a_1259_; uint8_t v___x_1265_; 
v___x_1265_ = lean_usize_dec_eq(v_i_1247_, v_stop_1248_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_array_uget_borrowed(v_as_1246_, v_i_1247_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_box(0);
v_a_1259_ = v___x_1267_;
goto v___jp_1258_;
}
else
{
lean_object* v_val_1268_; uint8_t v___y_1270_; uint8_t v___x_1297_; 
v_val_1268_ = lean_ctor_get(v___x_1266_, 0);
v___x_1297_ = l_Lean_LocalDecl_isLet(v_val_1268_, v___x_1265_);
if (v___x_1297_ == 0)
{
v___y_1270_ = v___x_1297_;
goto v___jp_1269_;
}
else
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1268_);
if (v___x_1298_ == 0)
{
v___y_1270_ = v___x_1297_;
goto v___jp_1269_;
}
else
{
goto v___jp_1263_;
}
}
v___jp_1269_:
{
if (v___y_1270_ == 0)
{
goto v___jp_1263_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_Lean_LocalDecl_value(v_val_1268_, v___x_1265_);
v___x_1272_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1271_, v___y_1254_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; lean_object* v_givenNames_1275_; lean_object* v_decls_1276_; lean_object* v_valueMap_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1288_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = lean_st_ref_take(v___y_1252_);
v_givenNames_1275_ = lean_ctor_get(v___x_1274_, 0);
v_decls_1276_ = lean_ctor_get(v___x_1274_, 1);
v_valueMap_1277_ = lean_ctor_get(v___x_1274_, 2);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1279_ = v___x_1274_;
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_valueMap_1277_);
lean_inc(v_decls_1276_);
lean_inc(v_givenNames_1275_);
lean_dec(v___x_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1281_ = l_Lean_LocalDecl_fvarId(v_val_1268_);
v___x_1282_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1277_, v_a_1273_, v___x_1281_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 2, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_givenNames_1275_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_decls_1276_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_st_ref_set(v___y_1252_, v___x_1284_);
v___x_1286_ = lean_box(0);
v_a_1259_ = v___x_1286_;
goto v___jp_1258_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1272_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1272_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_b_1249_);
return v___x_1299_;
}
v___jp_1258_:
{
size_t v___x_1260_; size_t v___x_1261_; 
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_add(v_i_1247_, v___x_1260_);
v_i_1247_ = v___x_1261_;
v_b_1249_ = v_a_1259_;
goto _start;
}
v___jp_1263_:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_box(0);
v_a_1259_ = v___x_1264_;
goto v___jp_1258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1300_, lean_object* v_i_1301_, lean_object* v_stop_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
size_t v_i_boxed_1312_; size_t v_stop_boxed_1313_; lean_object* v_res_1314_; 
v_i_boxed_1312_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_stop_boxed_1313_ = lean_unbox_usize(v_stop_1302_);
lean_dec(v_stop_1302_);
v_res_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1300_, v_i_boxed_1312_, v_stop_boxed_1313_, v_b_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_as_1300_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1315_, size_t v_i_1316_, size_t v_stop_1317_, lean_object* v_b_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_a_1328_; uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_eq(v_i_1316_, v_stop_1317_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_array_uget_borrowed(v_as_1315_, v_i_1316_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_box(0);
v_a_1328_ = v___x_1336_;
goto v___jp_1327_;
}
else
{
lean_object* v_val_1337_; uint8_t v___y_1339_; uint8_t v___x_1366_; 
v_val_1337_ = lean_ctor_get(v___x_1335_, 0);
v___x_1366_ = l_Lean_LocalDecl_isLet(v_val_1337_, v___x_1334_);
if (v___x_1366_ == 0)
{
v___y_1339_ = v___x_1366_;
goto v___jp_1338_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1337_);
if (v___x_1367_ == 0)
{
v___y_1339_ = v___x_1366_;
goto v___jp_1338_;
}
else
{
goto v___jp_1332_;
}
}
v___jp_1338_:
{
if (v___y_1339_ == 0)
{
goto v___jp_1332_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = l_Lean_LocalDecl_value(v_val_1337_, v___x_1334_);
v___x_1341_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1340_, v___y_1323_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v_givenNames_1344_; lean_object* v_decls_1345_; lean_object* v_valueMap_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1357_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_st_ref_take(v___y_1321_);
v_givenNames_1344_ = lean_ctor_get(v___x_1343_, 0);
v_decls_1345_ = lean_ctor_get(v___x_1343_, 1);
v_valueMap_1346_ = lean_ctor_get(v___x_1343_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1348_ = v___x_1343_;
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_valueMap_1346_);
lean_inc(v_decls_1345_);
lean_inc(v_givenNames_1344_);
lean_dec(v___x_1343_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = l_Lean_LocalDecl_fvarId(v_val_1337_);
v___x_1351_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1346_, v_a_1342_, v___x_1350_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 2, v___x_1351_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_givenNames_1344_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_decls_1345_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_st_ref_set(v___y_1321_, v___x_1353_);
v___x_1355_ = lean_box(0);
v_a_1328_ = v___x_1355_;
goto v___jp_1327_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_a_1358_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1341_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1341_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_b_1318_);
return v___x_1368_;
}
v___jp_1327_:
{
size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1316_, v___x_1329_);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1315_, v___x_1330_, v_stop_1317_, v_a_1328_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
return v___x_1331_;
}
v___jp_1332_:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_box(0);
v_a_1328_ = v___x_1333_;
goto v___jp_1327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1369_, lean_object* v_i_1370_, lean_object* v_stop_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
size_t v_i_boxed_1381_; size_t v_stop_boxed_1382_; lean_object* v_res_1383_; 
v_i_boxed_1381_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_stop_boxed_1382_ = lean_unbox_usize(v_stop_1371_);
lean_dec(v_stop_1371_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1369_, v_i_boxed_1381_, v_stop_boxed_1382_, v_b_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec_ref(v_as_1369_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v_cs_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1414_; 
v_cs_1393_ = lean_ctor_get(v_x_1384_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1395_ = v_x_1384_;
v_isShared_1396_ = v_isSharedCheck_1414_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_cs_1393_);
lean_dec(v_x_1384_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1414_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_array_get_size(v_cs_1393_);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_nat_dec_lt(v___x_1397_, v___x_1398_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1402_; 
lean_dec_ref(v_cs_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1399_);
v___x_1402_ = v___x_1395_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1399_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_le(v___x_1398_, v___x_1398_);
if (v___x_1404_ == 0)
{
if (v___x_1400_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_cs_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1399_);
v___x_1406_ = v___x_1395_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1399_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
lean_del_object(v___x_1395_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1398_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1393_, v___x_1408_, v___x_1409_, v___x_1399_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec_ref(v_cs_1393_);
return v___x_1410_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
lean_del_object(v___x_1395_);
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1398_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1393_, v___x_1411_, v___x_1412_, v___x_1399_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec_ref(v_cs_1393_);
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_vs_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1436_; 
v_vs_1415_ = lean_ctor_get(v_x_1384_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1417_ = v_x_1384_;
v_isShared_1418_ = v_isSharedCheck_1436_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_vs_1415_);
lean_dec(v_x_1384_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1436_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_array_get_size(v_vs_1415_);
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_nat_dec_lt(v___x_1419_, v___x_1420_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref(v_vs_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1421_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_nat_dec_le(v___x_1420_, v___x_1420_);
if (v___x_1426_ == 0)
{
if (v___x_1422_ == 0)
{
lean_object* v___x_1428_; 
lean_dec_ref(v_vs_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1428_ = v___x_1417_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1421_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
lean_del_object(v___x_1417_);
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_of_nat(v___x_1420_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1415_, v___x_1430_, v___x_1431_, v___x_1421_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec_ref(v_vs_1415_);
return v___x_1432_;
}
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
lean_del_object(v___x_1417_);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1420_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1415_, v___x_1433_, v___x_1434_, v___x_1421_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec_ref(v_vs_1415_);
return v___x_1435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1437_, size_t v_i_1438_, size_t v_stop_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_usize_dec_eq(v_i_1438_, v_stop_1439_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_array_uget_borrowed(v_as_1437_, v_i_1438_);
lean_inc(v___x_1450_);
v___x_1451_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1450_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; size_t v___x_1453_; size_t v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1438_, v___x_1453_);
v_i_1438_ = v___x_1454_;
v_b_1440_ = v_a_1452_;
goto _start;
}
else
{
return v___x_1451_;
}
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_b_1440_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1457_, lean_object* v_i_1458_, lean_object* v_stop_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
size_t v_i_boxed_1469_; size_t v_stop_boxed_1470_; lean_object* v_res_1471_; 
v_i_boxed_1469_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_stop_boxed_1470_ = lean_unbox_usize(v_stop_1459_);
lean_dec(v_stop_1459_);
v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1457_, v_i_boxed_1469_, v_stop_boxed_1470_, v_b_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v_as_1457_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_root_1491_; lean_object* v_tail_1492_; lean_object* v___x_1493_; 
v_root_1491_ = lean_ctor_get(v_t_1482_, 0);
lean_inc_ref(v_root_1491_);
v_tail_1492_ = lean_ctor_get(v_t_1482_, 1);
lean_inc_ref(v_tail_1492_);
lean_dec_ref(v_t_1482_);
v___x_1493_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1491_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v___x_1493_, 0);
lean_dec(v_unused_1515_);
v___x_1495_ = v___x_1493_;
v_isShared_1496_ = v_isSharedCheck_1514_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v___x_1493_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1514_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = lean_array_get_size(v_tail_1492_);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_nat_dec_lt(v___x_1497_, v___x_1498_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1502_; 
lean_dec_ref(v_tail_1492_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1499_);
v___x_1502_ = v___x_1495_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1499_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_nat_dec_le(v___x_1498_, v___x_1498_);
if (v___x_1504_ == 0)
{
if (v___x_1500_ == 0)
{
lean_object* v___x_1506_; 
lean_dec_ref(v_tail_1492_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1499_);
v___x_1506_ = v___x_1495_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1499_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
else
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
lean_del_object(v___x_1495_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = lean_usize_of_nat(v___x_1498_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1492_, v___x_1508_, v___x_1509_, v___x_1499_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec_ref(v_tail_1492_);
return v___x_1510_;
}
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
lean_del_object(v___x_1495_);
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = lean_usize_of_nat(v___x_1498_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1492_, v___x_1511_, v___x_1512_, v___x_1499_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec_ref(v_tail_1492_);
return v___x_1513_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1492_);
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1525_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1527_, size_t v_x_1528_, size_t v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_object* v_cs_1538_; lean_object* v___x_1539_; size_t v___x_1540_; lean_object* v_j_1541_; lean_object* v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v_cs_1538_ = lean_ctor_get(v_x_1527_, 0);
lean_inc_ref(v_cs_1538_);
lean_dec_ref(v_x_1527_);
v___x_1539_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1540_ = lean_usize_shift_right(v_x_1528_, v_x_1529_);
v_j_1541_ = lean_usize_to_nat(v___x_1540_);
v___x_1542_ = lean_array_get_borrowed(v___x_1539_, v_cs_1538_, v_j_1541_);
v___x_1543_ = ((size_t)1ULL);
v___x_1544_ = lean_usize_shift_left(v___x_1543_, v_x_1529_);
v___x_1545_ = lean_usize_sub(v___x_1544_, v___x_1543_);
v___x_1546_ = lean_usize_land(v_x_1528_, v___x_1545_);
v___x_1547_ = ((size_t)5ULL);
v___x_1548_ = lean_usize_sub(v_x_1529_, v___x_1547_);
lean_inc(v___x_1542_);
v___x_1549_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1542_, v___x_1546_, v___x_1548_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1571_; 
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v___x_1549_, 0);
lean_dec(v_unused_1572_);
v___x_1551_ = v___x_1549_;
v_isShared_1552_ = v_isSharedCheck_1571_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v___x_1549_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1571_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_nat_add(v_j_1541_, v___x_1553_);
lean_dec(v_j_1541_);
v___x_1555_ = lean_array_get_size(v_cs_1538_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_nat_dec_lt(v___x_1554_, v___x_1555_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1559_; 
lean_dec(v___x_1554_);
lean_dec_ref(v_cs_1538_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1556_);
v___x_1559_ = v___x_1551_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1556_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_nat_dec_le(v___x_1555_, v___x_1555_);
if (v___x_1561_ == 0)
{
if (v___x_1557_ == 0)
{
lean_object* v___x_1563_; 
lean_dec(v___x_1554_);
lean_dec_ref(v_cs_1538_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1556_);
v___x_1563_ = v___x_1551_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1556_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
else
{
size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
lean_del_object(v___x_1551_);
v___x_1565_ = lean_usize_of_nat(v___x_1554_);
lean_dec(v___x_1554_);
v___x_1566_ = lean_usize_of_nat(v___x_1555_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1538_, v___x_1565_, v___x_1566_, v___x_1556_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec_ref(v_cs_1538_);
return v___x_1567_;
}
}
else
{
size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
lean_del_object(v___x_1551_);
v___x_1568_ = lean_usize_of_nat(v___x_1554_);
lean_dec(v___x_1554_);
v___x_1569_ = lean_usize_of_nat(v___x_1555_);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1538_, v___x_1568_, v___x_1569_, v___x_1556_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec_ref(v_cs_1538_);
return v___x_1570_;
}
}
}
}
else
{
lean_dec(v_j_1541_);
lean_dec_ref(v_cs_1538_);
return v___x_1549_;
}
}
else
{
lean_object* v_vs_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1594_; 
v_vs_1573_ = lean_ctor_get(v_x_1527_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1527_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1575_ = v_x_1527_;
v_isShared_1576_ = v_isSharedCheck_1594_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_vs_1573_);
lean_dec(v_x_1527_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1594_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1577_ = lean_usize_to_nat(v_x_1528_);
v___x_1578_ = lean_array_get_size(v_vs_1573_);
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_nat_dec_lt(v___x_1577_, v___x_1578_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1582_; 
lean_dec(v___x_1577_);
lean_dec_ref(v_vs_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1579_);
v___x_1582_ = v___x_1575_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
else
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_nat_dec_le(v___x_1578_, v___x_1578_);
if (v___x_1584_ == 0)
{
if (v___x_1580_ == 0)
{
lean_object* v___x_1586_; 
lean_dec(v___x_1577_);
lean_dec_ref(v_vs_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1579_);
v___x_1586_ = v___x_1575_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1579_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
lean_del_object(v___x_1575_);
v___x_1588_ = lean_usize_of_nat(v___x_1577_);
lean_dec(v___x_1577_);
v___x_1589_ = lean_usize_of_nat(v___x_1578_);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1573_, v___x_1588_, v___x_1589_, v___x_1579_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec_ref(v_vs_1573_);
return v___x_1590_;
}
}
else
{
size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
lean_del_object(v___x_1575_);
v___x_1591_ = lean_usize_of_nat(v___x_1577_);
lean_dec(v___x_1577_);
v___x_1592_ = lean_usize_of_nat(v___x_1578_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1573_, v___x_1591_, v___x_1592_, v___x_1579_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec_ref(v_vs_1573_);
return v___x_1593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
size_t v_x_10794__boxed_1606_; size_t v_x_10795__boxed_1607_; lean_object* v_res_1608_; 
v_x_10794__boxed_1606_ = lean_unbox_usize(v_x_1596_);
lean_dec(v_x_1596_);
v_x_10795__boxed_1607_ = lean_unbox_usize(v_x_1597_);
lean_dec(v_x_1597_);
v_res_1608_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1595_, v_x_10794__boxed_1606_, v_x_10795__boxed_1607_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1609_, lean_object* v_start_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_nat_dec_eq(v_start_1610_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v_root_1621_; lean_object* v_tail_1622_; size_t v_shift_1623_; lean_object* v_tailOff_1624_; uint8_t v___x_1625_; 
v_root_1621_ = lean_ctor_get(v_t_1609_, 0);
lean_inc_ref(v_root_1621_);
v_tail_1622_ = lean_ctor_get(v_t_1609_, 1);
lean_inc_ref(v_tail_1622_);
v_shift_1623_ = lean_ctor_get_usize(v_t_1609_, 4);
v_tailOff_1624_ = lean_ctor_get(v_t_1609_, 3);
lean_inc(v_tailOff_1624_);
lean_dec_ref(v_t_1609_);
v___x_1625_ = lean_nat_dec_le(v_tailOff_1624_, v_start_1610_);
if (v___x_1625_ == 0)
{
size_t v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_tailOff_1624_);
v___x_1626_ = lean_usize_of_nat(v_start_1610_);
v___x_1627_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1621_, v___x_1626_, v_shift_1623_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1647_; 
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v___x_1627_, 0);
lean_dec(v_unused_1648_);
v___x_1629_ = v___x_1627_;
v_isShared_1630_ = v_isSharedCheck_1647_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v___x_1627_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1647_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = lean_array_get_size(v_tail_1622_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_nat_dec_lt(v___x_1619_, v___x_1631_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref(v_tail_1622_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1632_);
v___x_1635_ = v___x_1629_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1632_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
else
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_nat_dec_le(v___x_1631_, v___x_1631_);
if (v___x_1637_ == 0)
{
if (v___x_1633_ == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v_tail_1622_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1632_);
v___x_1639_ = v___x_1629_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1632_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
lean_del_object(v___x_1629_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = lean_usize_of_nat(v___x_1631_);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1622_, v___x_1641_, v___x_1642_, v___x_1632_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v_tail_1622_);
return v___x_1643_;
}
}
else
{
size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
lean_del_object(v___x_1629_);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = lean_usize_of_nat(v___x_1631_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1622_, v___x_1644_, v___x_1645_, v___x_1632_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v_tail_1622_);
return v___x_1646_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1622_);
return v___x_1627_;
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
lean_dec_ref(v_root_1621_);
v___x_1649_ = lean_nat_sub(v_start_1610_, v_tailOff_1624_);
lean_dec(v_tailOff_1624_);
v___x_1650_ = lean_array_get_size(v_tail_1622_);
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_nat_dec_lt(v___x_1649_, v___x_1650_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec(v___x_1649_);
lean_dec_ref(v_tail_1622_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
return v___x_1653_;
}
else
{
uint8_t v___x_1654_; 
v___x_1654_ = lean_nat_dec_le(v___x_1650_, v___x_1650_);
if (v___x_1654_ == 0)
{
if (v___x_1652_ == 0)
{
lean_object* v___x_1655_; 
lean_dec(v___x_1649_);
lean_dec_ref(v_tail_1622_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1651_);
return v___x_1655_;
}
else
{
size_t v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_usize_of_nat(v___x_1649_);
lean_dec(v___x_1649_);
v___x_1657_ = lean_usize_of_nat(v___x_1650_);
v___x_1658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1622_, v___x_1656_, v___x_1657_, v___x_1651_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v_tail_1622_);
return v___x_1658_;
}
}
else
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_usize_of_nat(v___x_1649_);
lean_dec(v___x_1649_);
v___x_1660_ = lean_usize_of_nat(v___x_1650_);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1622_, v___x_1659_, v___x_1660_, v___x_1651_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v_tail_1622_);
return v___x_1661_;
}
}
}
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1609_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1663_, lean_object* v_start_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1663_, v_start_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v_start_1664_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1674_, lean_object* v_start_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_decls_1684_; lean_object* v___x_1685_; 
v_decls_1684_ = lean_ctor_get(v_lctx_1674_, 1);
lean_inc_ref(v_decls_1684_);
lean_dec_ref(v_lctx_1674_);
v___x_1685_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1684_, v_start_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1686_, lean_object* v_start_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1686_, v_start_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v_start_1687_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_lctx_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_lctx_1705_ = lean_ctor_get(v_a_1700_, 2);
v___x_1706_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1705_);
v___x_1707_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1705_, v___x_1706_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
return v_res_1716_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1718_){
_start:
{
lean_object* v___f_1719_; lean_object* v___x_1720_; 
v___f_1719_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1720_ = lean_find_expr(v___f_1719_, v_e_1718_);
if (lean_obj_tag(v___x_1720_) == 0)
{
uint8_t v___x_1721_; 
v___x_1721_ = 0;
return v___x_1721_;
}
else
{
uint8_t v___x_1722_; 
lean_dec_ref(v___x_1720_);
v___x_1722_ = 1;
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1723_){
_start:
{
uint8_t v_res_1724_; lean_object* v_r_1725_; 
v_res_1724_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1723_);
lean_dec_ref(v_e_1723_);
v_r_1725_ = lean_box(v_res_1724_);
return v_r_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1729_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
v___x_1736_ = lean_apply_9(v_k_1726_, v_b_1730_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, lean_box(0));
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v_b_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v_b_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1748_, uint8_t v_bi_1749_, lean_object* v_type_1750_, lean_object* v_k_1751_, uint8_t v_kind_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___f_1761_; lean_object* v___x_1762_; 
lean_inc(v___y_1755_);
lean_inc(v___y_1754_);
lean_inc_ref(v___y_1753_);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1761_, 0, v_k_1751_);
lean_closure_set(v___f_1761_, 1, v___y_1753_);
lean_closure_set(v___f_1761_, 2, v___y_1754_);
lean_closure_set(v___f_1761_, 3, v___y_1755_);
v___x_1762_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1748_, v_bi_1749_, v_type_1750_, v___f_1761_, v_kind_1752_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1762_) == 0)
{
return v___x_1762_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1771_, lean_object* v_bi_1772_, lean_object* v_type_1773_, lean_object* v_k_1774_, lean_object* v_kind_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
uint8_t v_bi_boxed_1784_; uint8_t v_kind_boxed_1785_; lean_object* v_res_1786_; 
v_bi_boxed_1784_ = lean_unbox(v_bi_1772_);
v_kind_boxed_1785_ = lean_unbox(v_kind_1775_);
v_res_1786_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1771_, v_bi_boxed_1784_, v_type_1773_, v_k_1774_, v_kind_boxed_1785_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1787_, lean_object* v_name_1788_, uint8_t v_bi_1789_, lean_object* v_type_1790_, lean_object* v_k_1791_, uint8_t v_kind_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1788_, v_bi_1789_, v_type_1790_, v_k_1791_, v_kind_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_name_1803_, lean_object* v_bi_1804_, lean_object* v_type_1805_, lean_object* v_k_1806_, lean_object* v_kind_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v_bi_boxed_1816_; uint8_t v_kind_boxed_1817_; lean_object* v_res_1818_; 
v_bi_boxed_1816_ = lean_unbox(v_bi_1804_);
v_kind_boxed_1817_ = lean_unbox(v_kind_1807_);
v_res_1818_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1802_, v_name_1803_, v_bi_boxed_1816_, v_type_1805_, v_k_1806_, v_kind_boxed_1817_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1819_, lean_object* v_e_1820_, lean_object* v___f_1821_, lean_object* v_____r_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
if (v_types_1819_ == 0)
{
lean_object* v___x_1831_; 
lean_inc_ref(v_e_1820_);
v___x_1831_ = l_Lean_Meta_isType(v_e_1820_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1842_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_del_object(v___x_1834_);
lean_dec_ref(v_e_1820_);
v___x_1837_ = lean_box(0);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
v___x_1838_ = lean_apply_9(v___f_1821_, v___x_1837_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, lean_box(0));
return v___x_1838_;
}
else
{
lean_object* v___x_1840_; 
lean_dec_ref(v___f_1821_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_e_1820_);
v___x_1840_ = v___x_1834_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_e_1820_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref(v___f_1821_);
lean_dec_ref(v_e_1820_);
v_a_1843_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1831_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1831_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v_e_1820_);
v___x_1851_ = lean_box(0);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
v___x_1852_ = lean_apply_9(v___f_1821_, v___x_1851_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, lean_box(0));
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1853_, lean_object* v_e_1854_, lean_object* v___f_1855_, lean_object* v_____r_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v_types_boxed_1865_; lean_object* v_res_1866_; 
v_types_boxed_1865_ = lean_unbox(v_types_1853_);
v_res_1866_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1865_, v_e_1854_, v___f_1855_, v_____r_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1866_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1867_, uint8_t v___y_1868_){
_start:
{
if (v___y_1867_ == 0)
{
if (v___y_1868_ == 0)
{
uint8_t v___x_1869_; 
v___x_1869_ = 1;
return v___x_1869_;
}
else
{
return v___y_1867_;
}
}
else
{
return v___y_1868_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
uint8_t v___y_50691__boxed_1872_; uint8_t v___y_50692__boxed_1873_; uint8_t v_res_1874_; lean_object* v_r_1875_; 
v___y_50691__boxed_1872_ = lean_unbox(v___y_1870_);
v___y_50692__boxed_1873_ = lean_unbox(v___y_1871_);
v_res_1874_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_50691__boxed_1872_, v___y_50692__boxed_1873_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_instMonadEIO(lean_box(0));
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_toApplicative_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1967_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1895_ = l_StateRefT_x27_instMonad___redArg(v___x_1894_);
v_toApplicative_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1895_, 1);
lean_dec(v_unused_1968_);
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1967_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_toApplicative_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1967_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_toFunctor_1900_; lean_object* v_toSeq_1901_; lean_object* v_toSeqLeft_1902_; lean_object* v_toSeqRight_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1965_; 
v_toFunctor_1900_ = lean_ctor_get(v_toApplicative_1896_, 0);
v_toSeq_1901_ = lean_ctor_get(v_toApplicative_1896_, 2);
v_toSeqLeft_1902_ = lean_ctor_get(v_toApplicative_1896_, 3);
v_toSeqRight_1903_ = lean_ctor_get(v_toApplicative_1896_, 4);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_toApplicative_1896_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v_toApplicative_1896_, 1);
lean_dec(v_unused_1966_);
v___x_1905_ = v_toApplicative_1896_;
v_isShared_1906_ = v_isSharedCheck_1965_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_toSeqRight_1903_);
lean_inc(v_toSeqLeft_1902_);
lean_inc(v_toSeq_1901_);
lean_inc(v_toFunctor_1900_);
lean_dec(v_toApplicative_1896_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1965_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___f_1907_; lean_object* v___f_1908_; lean_object* v___f_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___f_1913_; lean_object* v___f_1914_; lean_object* v___x_1916_; 
v___f_1907_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1908_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1900_);
v___f_1909_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1909_, 0, v_toFunctor_1900_);
v___f_1910_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1910_, 0, v_toFunctor_1900_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___f_1909_);
lean_ctor_set(v___x_1911_, 1, v___f_1910_);
v___f_1912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1912_, 0, v_toSeqRight_1903_);
v___f_1913_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1913_, 0, v_toSeqLeft_1902_);
v___f_1914_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1914_, 0, v_toSeq_1901_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v___f_1912_);
lean_ctor_set(v___x_1905_, 3, v___f_1913_);
lean_ctor_set(v___x_1905_, 2, v___f_1914_);
lean_ctor_set(v___x_1905_, 1, v___f_1907_);
lean_ctor_set(v___x_1905_, 0, v___x_1911_);
v___x_1916_ = v___x_1905_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___f_1907_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v___f_1914_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v___f_1913_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v___f_1912_);
v___x_1916_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v___f_1908_);
lean_ctor_set(v___x_1898_, 0, v___x_1916_);
v___x_1918_ = v___x_1898_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___f_1908_);
v___x_1918_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v_toApplicative_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1961_; 
v___x_1919_ = l_StateRefT_x27_instMonad___redArg(v___x_1918_);
v_toApplicative_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1919_, 1);
lean_dec(v_unused_1962_);
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1961_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_toApplicative_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1961_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_toFunctor_1924_; lean_object* v_toSeq_1925_; lean_object* v_toSeqLeft_1926_; lean_object* v_toSeqRight_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1959_; 
v_toFunctor_1924_ = lean_ctor_get(v_toApplicative_1920_, 0);
v_toSeq_1925_ = lean_ctor_get(v_toApplicative_1920_, 2);
v_toSeqLeft_1926_ = lean_ctor_get(v_toApplicative_1920_, 3);
v_toSeqRight_1927_ = lean_ctor_get(v_toApplicative_1920_, 4);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_toApplicative_1920_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v_toApplicative_1920_, 1);
lean_dec(v_unused_1960_);
v___x_1929_ = v_toApplicative_1920_;
v_isShared_1930_ = v_isSharedCheck_1959_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_toSeqRight_1927_);
lean_inc(v_toSeqLeft_1926_);
lean_inc(v_toSeq_1925_);
lean_inc(v_toFunctor_1924_);
lean_dec(v_toApplicative_1920_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1959_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___f_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___f_1938_; lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___f_1945_; lean_object* v___x_1947_; 
v___f_1931_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1932_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1932_, 0, v___f_1931_);
v___x_1933_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1934_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1934_, 0, v___f_1932_);
lean_closure_set(v___f_1934_, 1, v___x_1933_);
v___f_1935_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1936_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1937_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1937_, 0, v___f_1935_);
lean_closure_set(v___f_1937_, 1, v___x_1936_);
v___f_1938_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1939_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1924_);
v___f_1940_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1940_, 0, v_toFunctor_1924_);
v___f_1941_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1941_, 0, v_toFunctor_1924_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___f_1940_);
lean_ctor_set(v___x_1942_, 1, v___f_1941_);
v___f_1943_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1943_, 0, v_toSeqRight_1927_);
v___f_1944_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1944_, 0, v_toSeqLeft_1926_);
v___f_1945_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1945_, 0, v_toSeq_1925_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 4, v___f_1943_);
lean_ctor_set(v___x_1929_, 3, v___f_1944_);
lean_ctor_set(v___x_1929_, 2, v___f_1945_);
lean_ctor_set(v___x_1929_, 1, v___f_1938_);
lean_ctor_set(v___x_1929_, 0, v___x_1942_);
v___x_1947_ = v___x_1929_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___f_1938_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v___f_1945_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v___f_1944_);
lean_ctor_set(v_reuseFailAlloc_1958_, 4, v___f_1943_);
v___x_1947_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___f_1939_);
lean_ctor_set(v___x_1922_, 0, v___x_1947_);
v___x_1949_ = v___x_1922_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___f_1939_);
v___x_1949_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___f_1954_; lean_object* v___x_47579__overap_1955_; lean_object* v___x_1956_; 
v___x_1950_ = l_StateRefT_x27_instMonad___redArg(v___x_1949_);
v___x_1951_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1893_, v___f_1934_, v___f_1937_, v___x_1950_);
v___x_1952_ = l_Lean_instInhabitedExpr;
v___x_1953_ = l_instInhabitedOfMonad___redArg(v___x_1951_, v___x_1952_);
v___f_1954_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1954_, 0, v___x_1953_);
v___x_47579__overap_1955_ = lean_panic_fn_borrowed(v___f_1954_, v_msg_1884_);
lean_dec_ref(v___f_1954_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
v___x_1956_ = lean_apply_8(v___x_47579__overap_1955_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, lean_box(0));
return v___x_1956_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderName_1979_, uint8_t v_binderInfo_1980_, lean_object* v_e_1981_, lean_object* v_binderType_1982_, lean_object* v_body_1983_, lean_object* v_t_1984_, lean_object* v_b_1985_){
_start:
{
uint8_t v___y_1987_; size_t v___x_1991_; size_t v___x_1992_; uint8_t v___x_1993_; 
v___x_1991_ = lean_ptr_addr(v_binderType_1982_);
v___x_1992_ = lean_ptr_addr(v_t_1984_);
v___x_1993_ = lean_usize_dec_eq(v___x_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
v___y_1987_ = v___x_1993_;
goto v___jp_1986_;
}
else
{
size_t v___x_1994_; size_t v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = lean_ptr_addr(v_body_1983_);
v___x_1995_ = lean_ptr_addr(v_b_1985_);
v___x_1996_ = lean_usize_dec_eq(v___x_1994_, v___x_1995_);
v___y_1987_ = v___x_1996_;
goto v___jp_1986_;
}
v___jp_1986_:
{
if (v___y_1987_ == 0)
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Expr_lam___override(v_binderName_1979_, v_t_1984_, v_b_1985_, v_binderInfo_1980_);
return v___x_1988_;
}
else
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1980_, v_binderInfo_1980_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Expr_lam___override(v_binderName_1979_, v_t_1984_, v_b_1985_, v_binderInfo_1980_);
return v___x_1990_;
}
else
{
lean_dec_ref(v_b_1985_);
lean_dec_ref(v_t_1984_);
lean_dec(v_binderName_1979_);
lean_inc_ref(v_e_1981_);
return v_e_1981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderName_1997_, lean_object* v_binderInfo_1998_, lean_object* v_e_1999_, lean_object* v_binderType_2000_, lean_object* v_body_2001_, lean_object* v_t_2002_, lean_object* v_b_2003_){
_start:
{
uint8_t v_binderInfo_50878__boxed_2004_; lean_object* v_res_2005_; 
v_binderInfo_50878__boxed_2004_ = lean_unbox(v_binderInfo_1998_);
v_res_2005_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderName_1997_, v_binderInfo_50878__boxed_2004_, v_e_1999_, v_binderType_2000_, v_body_2001_, v_t_2002_, v_b_2003_);
lean_dec_ref(v_body_2001_);
lean_dec_ref(v_binderType_2000_);
lean_dec_ref(v_e_1999_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderName_2006_, uint8_t v_binderInfo_2007_, lean_object* v_e_2008_, lean_object* v_binderType_2009_, lean_object* v_body_2010_, lean_object* v_t_2011_, lean_object* v_b_2012_){
_start:
{
uint8_t v___y_2014_; size_t v___x_2018_; size_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2018_ = lean_ptr_addr(v_binderType_2009_);
v___x_2019_ = lean_ptr_addr(v_t_2011_);
v___x_2020_ = lean_usize_dec_eq(v___x_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
v___y_2014_ = v___x_2020_;
goto v___jp_2013_;
}
else
{
size_t v___x_2021_; size_t v___x_2022_; uint8_t v___x_2023_; 
v___x_2021_ = lean_ptr_addr(v_body_2010_);
v___x_2022_ = lean_ptr_addr(v_b_2012_);
v___x_2023_ = lean_usize_dec_eq(v___x_2021_, v___x_2022_);
v___y_2014_ = v___x_2023_;
goto v___jp_2013_;
}
v___jp_2013_:
{
if (v___y_2014_ == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Expr_forallE___override(v_binderName_2006_, v_t_2011_, v_b_2012_, v_binderInfo_2007_);
return v___x_2015_;
}
else
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2007_, v_binderInfo_2007_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Expr_forallE___override(v_binderName_2006_, v_t_2011_, v_b_2012_, v_binderInfo_2007_);
return v___x_2017_;
}
else
{
lean_dec_ref(v_b_2012_);
lean_dec_ref(v_t_2011_);
lean_dec(v_binderName_2006_);
lean_inc_ref(v_e_2008_);
return v_e_2008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderName_2024_, lean_object* v_binderInfo_2025_, lean_object* v_e_2026_, lean_object* v_binderType_2027_, lean_object* v_body_2028_, lean_object* v_t_2029_, lean_object* v_b_2030_){
_start:
{
uint8_t v_binderInfo_50912__boxed_2031_; lean_object* v_res_2032_; 
v_binderInfo_50912__boxed_2031_ = lean_unbox(v_binderInfo_2025_);
v_res_2032_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderName_2024_, v_binderInfo_50912__boxed_2031_, v_e_2026_, v_binderType_2027_, v_body_2028_, v_t_2029_, v_b_2030_);
lean_dec_ref(v_body_2028_);
lean_dec_ref(v_binderType_2027_);
lean_dec_ref(v_e_2026_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_2033_, lean_object* v_type_2034_, lean_object* v_val_2035_, lean_object* v_k_2036_, uint8_t v_nondep_2037_, uint8_t v_kind_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___f_2047_; lean_object* v___x_2048_; 
lean_inc(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
v___f_2047_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2047_, 0, v_k_2036_);
lean_closure_set(v___f_2047_, 1, v___y_2039_);
lean_closure_set(v___f_2047_, 2, v___y_2040_);
lean_closure_set(v___f_2047_, 3, v___y_2041_);
v___x_2048_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2033_, v_type_2034_, v_val_2035_, v___f_2047_, v_nondep_2037_, v_kind_2038_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2048_) == 0)
{
return v___x_2048_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2057_, lean_object* v_type_2058_, lean_object* v_val_2059_, lean_object* v_k_2060_, lean_object* v_nondep_2061_, lean_object* v_kind_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
uint8_t v_nondep_boxed_2071_; uint8_t v_kind_boxed_2072_; lean_object* v_res_2073_; 
v_nondep_boxed_2071_ = lean_unbox(v_nondep_2061_);
v_kind_boxed_2072_ = lean_unbox(v_kind_2062_);
v_res_2073_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2057_, v_type_2058_, v_val_2059_, v_k_2060_, v_nondep_boxed_2071_, v_kind_boxed_2072_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = l_Lean_instInhabitedExpr;
v___x_2076_ = lean_panic_fn_borrowed(v___x_2075_, v_msg_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2077_, lean_object* v_x_2078_){
_start:
{
if (lean_obj_tag(v_x_2078_) == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_box(0);
return v___x_2079_;
}
else
{
lean_object* v_key_2080_; lean_object* v_value_2081_; lean_object* v_tail_2082_; uint8_t v___x_2083_; 
v_key_2080_ = lean_ctor_get(v_x_2078_, 0);
v_value_2081_ = lean_ctor_get(v_x_2078_, 1);
v_tail_2082_ = lean_ctor_get(v_x_2078_, 2);
v___x_2083_ = l_Lean_ExprStructEq_beq(v_key_2080_, v_a_2077_);
if (v___x_2083_ == 0)
{
v_x_2078_ = v_tail_2082_;
goto _start;
}
else
{
lean_object* v___x_2085_; 
lean_inc(v_value_2081_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_value_2081_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2086_, lean_object* v_x_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2086_, v_x_2087_);
lean_dec(v_x_2087_);
lean_dec_ref(v_a_2086_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_buckets_2091_; lean_object* v___x_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; uint64_t v___x_2095_; uint64_t v_fold_2096_; uint64_t v___x_2097_; uint64_t v___x_2098_; uint64_t v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_buckets_2091_ = lean_ctor_get(v_m_2089_, 1);
v___x_2092_ = lean_array_get_size(v_buckets_2091_);
v___x_2093_ = l_Lean_ExprStructEq_hash(v_a_2090_);
v___x_2094_ = 32ULL;
v___x_2095_ = lean_uint64_shift_right(v___x_2093_, v___x_2094_);
v_fold_2096_ = lean_uint64_xor(v___x_2093_, v___x_2095_);
v___x_2097_ = 16ULL;
v___x_2098_ = lean_uint64_shift_right(v_fold_2096_, v___x_2097_);
v___x_2099_ = lean_uint64_xor(v_fold_2096_, v___x_2098_);
v___x_2100_ = lean_uint64_to_usize(v___x_2099_);
v___x_2101_ = lean_usize_of_nat(v___x_2092_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_sub(v___x_2101_, v___x_2102_);
v___x_2104_ = lean_usize_land(v___x_2100_, v___x_2103_);
v___x_2105_ = lean_array_uget_borrowed(v_buckets_2091_, v___x_2104_);
v___x_2106_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2090_, v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2107_, v_a_2108_);
lean_dec_ref(v_a_2108_);
lean_dec_ref(v_m_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2110_, lean_object* v_x_2111_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
uint8_t v___x_2112_; 
v___x_2112_ = 0;
return v___x_2112_;
}
else
{
lean_object* v_key_2113_; lean_object* v_tail_2114_; lean_object* v_fst_2115_; lean_object* v_snd_2116_; lean_object* v_fst_2117_; lean_object* v_snd_2118_; uint8_t v___x_2122_; 
v_key_2113_ = lean_ctor_get(v_x_2111_, 0);
v_tail_2114_ = lean_ctor_get(v_x_2111_, 2);
v_fst_2115_ = lean_ctor_get(v_key_2113_, 0);
v_snd_2116_ = lean_ctor_get(v_key_2113_, 1);
v_fst_2117_ = lean_ctor_get(v_a_2110_, 0);
v_snd_2118_ = lean_ctor_get(v_a_2110_, 1);
v___x_2122_ = lean_unbox(v_fst_2115_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_unbox(v_fst_2117_);
if (v___x_2123_ == 0)
{
goto v___jp_2119_;
}
else
{
v_x_2111_ = v_tail_2114_;
goto _start;
}
}
else
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_unbox(v_fst_2117_);
if (v___x_2125_ == 0)
{
v_x_2111_ = v_tail_2114_;
goto _start;
}
else
{
goto v___jp_2119_;
}
}
v___jp_2119_:
{
uint8_t v___x_2120_; 
v___x_2120_ = l_Lean_ExprStructEq_beq(v_snd_2116_, v_snd_2118_);
if (v___x_2120_ == 0)
{
v_x_2111_ = v_tail_2114_;
goto _start;
}
else
{
return v___x_2120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2127_, lean_object* v_x_2128_){
_start:
{
uint8_t v_res_2129_; lean_object* v_r_2130_; 
v_res_2129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2127_, v_x_2128_);
lean_dec(v_x_2128_);
lean_dec_ref(v_a_2127_);
v_r_2130_ = lean_box(v_res_2129_);
return v_r_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2131_, lean_object* v_b_2132_, lean_object* v_x_2133_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_dec(v_b_2132_);
lean_dec_ref(v_a_2131_);
return v_x_2133_;
}
else
{
lean_object* v_key_2134_; lean_object* v_value_2135_; lean_object* v_tail_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2155_; 
v_key_2134_ = lean_ctor_get(v_x_2133_, 0);
v_value_2135_ = lean_ctor_get(v_x_2133_, 1);
v_tail_2136_ = lean_ctor_get(v_x_2133_, 2);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_x_2133_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2138_ = v_x_2133_;
v_isShared_2139_ = v_isSharedCheck_2155_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_tail_2136_);
lean_inc(v_value_2135_);
lean_inc(v_key_2134_);
lean_dec(v_x_2133_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2155_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_fst_2145_; lean_object* v_snd_2146_; lean_object* v_fst_2147_; lean_object* v_snd_2148_; uint8_t v___x_2152_; 
v_fst_2145_ = lean_ctor_get(v_key_2134_, 0);
v_snd_2146_ = lean_ctor_get(v_key_2134_, 1);
v_fst_2147_ = lean_ctor_get(v_a_2131_, 0);
v_snd_2148_ = lean_ctor_get(v_a_2131_, 1);
v___x_2152_ = lean_unbox(v_fst_2145_);
if (v___x_2152_ == 0)
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_unbox(v_fst_2147_);
if (v___x_2153_ == 0)
{
goto v___jp_2149_;
}
else
{
goto v___jp_2140_;
}
}
else
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_unbox(v_fst_2147_);
if (v___x_2154_ == 0)
{
goto v___jp_2140_;
}
else
{
goto v___jp_2149_;
}
}
v___jp_2140_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2131_, v_b_2132_, v_tail_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 2, v___x_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_key_2134_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_value_2135_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
v___jp_2149_:
{
uint8_t v___x_2150_; 
v___x_2150_ = l_Lean_ExprStructEq_beq(v_snd_2146_, v_snd_2148_);
if (v___x_2150_ == 0)
{
goto v___jp_2140_;
}
else
{
lean_object* v___x_2151_; 
lean_del_object(v___x_2138_);
lean_dec(v_value_2135_);
lean_dec(v_key_2134_);
v___x_2151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2151_, 0, v_a_2131_);
lean_ctor_set(v___x_2151_, 1, v_b_2132_);
lean_ctor_set(v___x_2151_, 2, v_tail_2136_);
return v___x_2151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
if (lean_obj_tag(v_x_2157_) == 0)
{
return v_x_2156_;
}
else
{
lean_object* v_key_2158_; lean_object* v_value_2159_; lean_object* v_tail_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2191_; 
v_key_2158_ = lean_ctor_get(v_x_2157_, 0);
v_value_2159_ = lean_ctor_get(v_x_2157_, 1);
v_tail_2160_ = lean_ctor_get(v_x_2157_, 2);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_x_2157_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2162_ = v_x_2157_;
v_isShared_2163_ = v_isSharedCheck_2191_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_tail_2160_);
lean_inc(v_value_2159_);
lean_inc(v_key_2158_);
lean_dec(v_x_2157_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2191_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_fst_2164_; lean_object* v_snd_2165_; lean_object* v___x_2166_; uint64_t v___y_2168_; uint8_t v___x_2188_; 
v_fst_2164_ = lean_ctor_get(v_key_2158_, 0);
v_snd_2165_ = lean_ctor_get(v_key_2158_, 1);
v___x_2166_ = lean_array_get_size(v_x_2156_);
v___x_2188_ = lean_unbox(v_fst_2164_);
if (v___x_2188_ == 0)
{
uint64_t v___x_2189_; 
v___x_2189_ = 13ULL;
v___y_2168_ = v___x_2189_;
goto v___jp_2167_;
}
else
{
uint64_t v___x_2190_; 
v___x_2190_ = 11ULL;
v___y_2168_ = v___x_2190_;
goto v___jp_2167_;
}
v___jp_2167_:
{
uint64_t v___x_2169_; uint64_t v___x_2170_; uint64_t v___x_2171_; uint64_t v___x_2172_; uint64_t v_fold_2173_; uint64_t v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2169_ = l_Lean_ExprStructEq_hash(v_snd_2165_);
v___x_2170_ = lean_uint64_mix_hash(v___y_2168_, v___x_2169_);
v___x_2171_ = 32ULL;
v___x_2172_ = lean_uint64_shift_right(v___x_2170_, v___x_2171_);
v_fold_2173_ = lean_uint64_xor(v___x_2170_, v___x_2172_);
v___x_2174_ = 16ULL;
v___x_2175_ = lean_uint64_shift_right(v_fold_2173_, v___x_2174_);
v___x_2176_ = lean_uint64_xor(v_fold_2173_, v___x_2175_);
v___x_2177_ = lean_uint64_to_usize(v___x_2176_);
v___x_2178_ = lean_usize_of_nat(v___x_2166_);
v___x_2179_ = ((size_t)1ULL);
v___x_2180_ = lean_usize_sub(v___x_2178_, v___x_2179_);
v___x_2181_ = lean_usize_land(v___x_2177_, v___x_2180_);
v___x_2182_ = lean_array_uget_borrowed(v_x_2156_, v___x_2181_);
lean_inc(v___x_2182_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 2, v___x_2182_);
v___x_2184_ = v___x_2162_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_key_2158_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_value_2159_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_array_uset(v_x_2156_, v___x_2181_, v___x_2184_);
v_x_2156_ = v___x_2185_;
v_x_2157_ = v_tail_2160_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2192_, lean_object* v_source_2193_, lean_object* v_target_2194_){
_start:
{
lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = lean_array_get_size(v_source_2193_);
v___x_2196_ = lean_nat_dec_lt(v_i_2192_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_dec_ref(v_source_2193_);
lean_dec(v_i_2192_);
return v_target_2194_;
}
else
{
lean_object* v_es_2197_; lean_object* v___x_2198_; lean_object* v_source_2199_; lean_object* v_target_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_es_2197_ = lean_array_fget(v_source_2193_, v_i_2192_);
v___x_2198_ = lean_box(0);
v_source_2199_ = lean_array_fset(v_source_2193_, v_i_2192_, v___x_2198_);
v_target_2200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2194_, v_es_2197_);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_add(v_i_2192_, v___x_2201_);
lean_dec(v_i_2192_);
v_i_2192_ = v___x_2202_;
v_source_2193_ = v_source_2199_;
v_target_2194_ = v_target_2200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2204_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v_nbuckets_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2205_ = lean_array_get_size(v_data_2204_);
v___x_2206_ = lean_unsigned_to_nat(2u);
v_nbuckets_2207_ = lean_nat_mul(v___x_2205_, v___x_2206_);
v___x_2208_ = lean_unsigned_to_nat(0u);
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_mk_array(v_nbuckets_2207_, v___x_2209_);
v___x_2211_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2208_, v_data_2204_, v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2212_, lean_object* v_a_2213_, lean_object* v_b_2214_){
_start:
{
lean_object* v_size_2215_; lean_object* v_buckets_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2267_; 
v_size_2215_ = lean_ctor_get(v_m_2212_, 0);
v_buckets_2216_ = lean_ctor_get(v_m_2212_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_m_2212_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2218_ = v_m_2212_;
v_isShared_2219_ = v_isSharedCheck_2267_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_buckets_2216_);
lean_inc(v_size_2215_);
lean_dec(v_m_2212_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2267_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_fst_2220_; lean_object* v_snd_2221_; lean_object* v___x_2222_; uint64_t v___y_2224_; uint8_t v___x_2264_; 
v_fst_2220_ = lean_ctor_get(v_a_2213_, 0);
v_snd_2221_ = lean_ctor_get(v_a_2213_, 1);
v___x_2222_ = lean_array_get_size(v_buckets_2216_);
v___x_2264_ = lean_unbox(v_fst_2220_);
if (v___x_2264_ == 0)
{
uint64_t v___x_2265_; 
v___x_2265_ = 13ULL;
v___y_2224_ = v___x_2265_;
goto v___jp_2223_;
}
else
{
uint64_t v___x_2266_; 
v___x_2266_ = 11ULL;
v___y_2224_ = v___x_2266_;
goto v___jp_2223_;
}
v___jp_2223_:
{
uint64_t v___x_2225_; uint64_t v___x_2226_; uint64_t v___x_2227_; uint64_t v___x_2228_; uint64_t v_fold_2229_; uint64_t v___x_2230_; uint64_t v___x_2231_; uint64_t v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; size_t v___x_2237_; lean_object* v_bkt_2238_; uint8_t v___x_2239_; 
v___x_2225_ = l_Lean_ExprStructEq_hash(v_snd_2221_);
v___x_2226_ = lean_uint64_mix_hash(v___y_2224_, v___x_2225_);
v___x_2227_ = 32ULL;
v___x_2228_ = lean_uint64_shift_right(v___x_2226_, v___x_2227_);
v_fold_2229_ = lean_uint64_xor(v___x_2226_, v___x_2228_);
v___x_2230_ = 16ULL;
v___x_2231_ = lean_uint64_shift_right(v_fold_2229_, v___x_2230_);
v___x_2232_ = lean_uint64_xor(v_fold_2229_, v___x_2231_);
v___x_2233_ = lean_uint64_to_usize(v___x_2232_);
v___x_2234_ = lean_usize_of_nat(v___x_2222_);
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_sub(v___x_2234_, v___x_2235_);
v___x_2237_ = lean_usize_land(v___x_2233_, v___x_2236_);
v_bkt_2238_ = lean_array_uget_borrowed(v_buckets_2216_, v___x_2237_);
v___x_2239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2213_, v_bkt_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v_size_x27_2241_; lean_object* v___x_2242_; lean_object* v_buckets_x27_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2240_ = lean_unsigned_to_nat(1u);
v_size_x27_2241_ = lean_nat_add(v_size_2215_, v___x_2240_);
lean_dec(v_size_2215_);
lean_inc(v_bkt_2238_);
v___x_2242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2213_);
lean_ctor_set(v___x_2242_, 1, v_b_2214_);
lean_ctor_set(v___x_2242_, 2, v_bkt_2238_);
v_buckets_x27_2243_ = lean_array_uset(v_buckets_2216_, v___x_2237_, v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(4u);
v___x_2245_ = lean_nat_mul(v_size_x27_2241_, v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(3u);
v___x_2247_ = lean_nat_div(v___x_2245_, v___x_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_array_get_size(v_buckets_x27_2243_);
v___x_2249_ = lean_nat_dec_le(v___x_2247_, v___x_2248_);
lean_dec(v___x_2247_);
if (v___x_2249_ == 0)
{
lean_object* v_val_2250_; lean_object* v___x_2252_; 
v_val_2250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2243_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_val_2250_);
lean_ctor_set(v___x_2218_, 0, v_size_x27_2241_);
v___x_2252_ = v___x_2218_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_size_x27_2241_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_val_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
else
{
lean_object* v___x_2255_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_buckets_x27_2243_);
lean_ctor_set(v___x_2218_, 0, v_size_x27_2241_);
v___x_2255_ = v___x_2218_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_size_x27_2241_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_buckets_x27_2243_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_object* v___x_2257_; lean_object* v_buckets_x27_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_inc(v_bkt_2238_);
v___x_2257_ = lean_box(0);
v_buckets_x27_2258_ = lean_array_uset(v_buckets_2216_, v___x_2237_, v___x_2257_);
v___x_2259_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2213_, v_b_2214_, v_bkt_2238_);
v___x_2260_ = lean_array_uset(v_buckets_x27_2258_, v___x_2237_, v___x_2259_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2260_);
v___x_2262_ = v___x_2218_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_size_2215_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2268_, lean_object* v_x_2269_){
_start:
{
if (lean_obj_tag(v_x_2269_) == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_box(0);
return v___x_2270_;
}
else
{
lean_object* v_key_2271_; lean_object* v_value_2272_; lean_object* v_tail_2273_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v_fst_2276_; lean_object* v_snd_2277_; uint8_t v___x_2282_; 
v_key_2271_ = lean_ctor_get(v_x_2269_, 0);
v_value_2272_ = lean_ctor_get(v_x_2269_, 1);
v_tail_2273_ = lean_ctor_get(v_x_2269_, 2);
v_fst_2274_ = lean_ctor_get(v_key_2271_, 0);
v_snd_2275_ = lean_ctor_get(v_key_2271_, 1);
v_fst_2276_ = lean_ctor_get(v_a_2268_, 0);
v_snd_2277_ = lean_ctor_get(v_a_2268_, 1);
v___x_2282_ = lean_unbox(v_fst_2274_);
if (v___x_2282_ == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_unbox(v_fst_2276_);
if (v___x_2283_ == 0)
{
goto v___jp_2278_;
}
else
{
v_x_2269_ = v_tail_2273_;
goto _start;
}
}
else
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_unbox(v_fst_2276_);
if (v___x_2285_ == 0)
{
v_x_2269_ = v_tail_2273_;
goto _start;
}
else
{
goto v___jp_2278_;
}
}
v___jp_2278_:
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Lean_ExprStructEq_beq(v_snd_2275_, v_snd_2277_);
if (v___x_2279_ == 0)
{
v_x_2269_ = v_tail_2273_;
goto _start;
}
else
{
lean_object* v___x_2281_; 
lean_inc(v_value_2272_);
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v_value_2272_);
return v___x_2281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2287_, v_x_2288_);
lean_dec(v_x_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_buckets_2292_; lean_object* v_fst_2293_; lean_object* v_snd_2294_; lean_object* v___x_2295_; uint64_t v___y_2297_; uint8_t v___x_2313_; 
v_buckets_2292_ = lean_ctor_get(v_m_2290_, 1);
v_fst_2293_ = lean_ctor_get(v_a_2291_, 0);
v_snd_2294_ = lean_ctor_get(v_a_2291_, 1);
v___x_2295_ = lean_array_get_size(v_buckets_2292_);
v___x_2313_ = lean_unbox(v_fst_2293_);
if (v___x_2313_ == 0)
{
uint64_t v___x_2314_; 
v___x_2314_ = 13ULL;
v___y_2297_ = v___x_2314_;
goto v___jp_2296_;
}
else
{
uint64_t v___x_2315_; 
v___x_2315_ = 11ULL;
v___y_2297_ = v___x_2315_;
goto v___jp_2296_;
}
v___jp_2296_:
{
uint64_t v___x_2298_; uint64_t v___x_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v_fold_2302_; uint64_t v___x_2303_; uint64_t v___x_2304_; uint64_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2298_ = l_Lean_ExprStructEq_hash(v_snd_2294_);
v___x_2299_ = lean_uint64_mix_hash(v___y_2297_, v___x_2298_);
v___x_2300_ = 32ULL;
v___x_2301_ = lean_uint64_shift_right(v___x_2299_, v___x_2300_);
v_fold_2302_ = lean_uint64_xor(v___x_2299_, v___x_2301_);
v___x_2303_ = 16ULL;
v___x_2304_ = lean_uint64_shift_right(v_fold_2302_, v___x_2303_);
v___x_2305_ = lean_uint64_xor(v_fold_2302_, v___x_2304_);
v___x_2306_ = lean_uint64_to_usize(v___x_2305_);
v___x_2307_ = lean_usize_of_nat(v___x_2295_);
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_sub(v___x_2307_, v___x_2308_);
v___x_2310_ = lean_usize_land(v___x_2306_, v___x_2309_);
v___x_2311_ = lean_array_uget_borrowed(v_buckets_2292_, v___x_2310_);
v___x_2312_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2291_, v___x_2311_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2316_, v_a_2317_);
lean_dec_ref(v_a_2317_);
lean_dec_ref(v_m_2316_);
return v_res_2318_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2319_; lean_object* v_dummy_2320_; 
v___x_2319_ = lean_box(0);
v_dummy_2320_ = l_Lean_Expr_sort___override(v___x_2319_);
return v_dummy_2320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2321_, lean_object* v_fst_2322_, lean_object* v_fvars_2323_, lean_object* v_a_2324_, lean_object* v_b_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_a_2335_; uint8_t v___x_2339_; 
v___x_2339_ = lean_nat_dec_lt(v_a_2324_, v_upperBound_2321_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
lean_dec(v_a_2324_);
lean_dec(v_fvars_2323_);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v_b_2325_);
return v___x_2340_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v_binderInfo_2343_; uint8_t v___x_2344_; 
v___x_2341_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2342_ = lean_array_get_borrowed(v___x_2341_, v_fst_2322_, v_a_2324_);
v_binderInfo_2343_ = lean_ctor_get_uint8(v___x_2342_, sizeof(void*)*2);
v___x_2344_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2343_);
if (v___x_2344_ == 0)
{
v_a_2335_ = v_b_2325_;
goto v___jp_2334_;
}
else
{
uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2345_ = 0;
v___x_2346_ = l_Lean_instInhabitedExpr;
v___x_2347_ = lean_array_get_borrowed(v___x_2346_, v_b_2325_, v_a_2324_);
lean_inc(v___x_2347_);
lean_inc(v_fvars_2323_);
v___x_2348_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2323_, v___x_2347_, v___x_2345_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = lean_array_set(v_b_2325_, v_a_2324_, v_a_2349_);
v_a_2335_ = v___x_2350_;
goto v___jp_2334_;
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v_b_2325_);
lean_dec(v_a_2324_);
lean_dec(v_fvars_2323_);
v_a_2351_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2348_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2348_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
v___jp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_add(v_a_2324_, v___x_2336_);
lean_dec(v_a_2324_);
v_a_2324_ = v___x_2337_;
v_b_2325_ = v_a_2335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2359_, size_t v_sz_2360_, size_t v_i_2361_, lean_object* v_bs_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = lean_usize_dec_lt(v_i_2361_, v_sz_2360_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; 
lean_dec(v_fvars_2359_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_bs_2362_);
return v___x_2372_;
}
else
{
uint8_t v___x_2373_; lean_object* v_v_2374_; lean_object* v___x_2375_; 
v___x_2373_ = 0;
v_v_2374_ = lean_array_uget_borrowed(v_bs_2362_, v_i_2361_);
lean_inc(v_v_2374_);
lean_inc(v_fvars_2359_);
v___x_2375_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2359_, v_v_2374_, v___x_2373_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; lean_object* v_bs_x27_2378_; size_t v___x_2379_; size_t v___x_2380_; lean_object* v___x_2381_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = lean_unsigned_to_nat(0u);
v_bs_x27_2378_ = lean_array_uset(v_bs_2362_, v_i_2361_, v___x_2377_);
v___x_2379_ = ((size_t)1ULL);
v___x_2380_ = lean_usize_add(v_i_2361_, v___x_2379_);
v___x_2381_ = lean_array_uset(v_bs_x27_2378_, v_i_2361_, v_a_2376_);
v_i_2361_ = v___x_2380_;
v_bs_2362_ = v___x_2381_;
goto _start;
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v_bs_2362_);
lean_dec(v_fvars_2359_);
v_a_2383_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2375_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2375_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2391_, lean_object* v_f_2392_, lean_object* v_args_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
uint8_t v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = 0;
lean_inc_ref(v_f_2392_);
lean_inc(v_fvars_2391_);
v___x_2403_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2391_, v_f_2392_, v___x_2402_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2403_) == 0)
{
uint8_t v_implicits_2404_; 
v_implicits_2404_ = lean_ctor_get_uint8(v_a_2394_, 2);
if (v_implicits_2404_ == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2403_);
lean_inc(v_a_2400_);
lean_inc_ref(v_a_2399_);
lean_inc(v_a_2398_);
lean_inc_ref(v_a_2397_);
v___x_2406_ = lean_infer_type(v_f_2392_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v___x_2408_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2407_, v_args_2393_, v___x_2402_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v_fst_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref(v___x_2408_);
v_fst_2410_ = lean_ctor_get(v_a_2409_, 0);
lean_inc(v_fst_2410_);
lean_dec(v_a_2409_);
v___x_2411_ = lean_array_get_size(v_args_2393_);
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2411_, v_fst_2410_, v_fvars_2391_, v___x_2412_, v_args_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_fst_2410_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2422_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = l_Lean_mkAppN(v_a_2405_, v_a_2414_);
lean_dec(v_a_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2418_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_a_2405_);
v_a_2423_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2413_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2413_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_a_2405_);
lean_dec_ref(v_args_2393_);
lean_dec(v_fvars_2391_);
v_a_2431_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2408_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2408_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_dec(v_a_2405_);
lean_dec_ref(v_args_2393_);
lean_dec(v_fvars_2391_);
return v___x_2406_;
}
}
else
{
lean_object* v_a_2439_; size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v_f_2392_);
v_a_2439_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2403_);
v_sz_2440_ = lean_array_size(v_args_2393_);
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2391_, v_sz_2440_, v___x_2441_, v_args_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = l_Lean_mkAppN(v_a_2439_, v_a_2443_);
lean_dec(v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_a_2439_);
v_a_2452_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2393_);
lean_dec_ref(v_f_2392_);
lean_dec(v_fvars_2391_);
return v___x_2403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2460_, lean_object* v_f_2461_, lean_object* v_args_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2460_, v_f_2461_, v_args_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2472_, lean_object* v_b_2473_, uint8_t v___x_2474_, lean_object* v_mk_2475_, lean_object* v_a_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_inc_ref(v_x_2477_);
v___x_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_x_2477_);
lean_ctor_set(v___x_2486_, 1, v_fvars_2472_);
v___x_2487_ = lean_expr_instantiate1(v_b_2473_, v_x_2477_);
v___x_2488_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2486_, v___x_2487_, v___x_2474_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2488_) == 0)
{
uint8_t v_lift_2489_; 
v_lift_2489_ = lean_ctor_get_uint8(v___y_2478_, 10);
if (v_lift_2489_ == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2502_; 
v_a_2490_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2492_ = v___x_2488_;
v_isShared_2493_ = v_isSharedCheck_2502_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2488_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2502_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2494_ = lean_unsigned_to_nat(1u);
v___x_2495_ = lean_mk_empty_array_with_capacity(v___x_2494_);
v___x_2496_ = lean_array_push(v___x_2495_, v_x_2477_);
v___x_2497_ = lean_expr_abstract(v_a_2490_, v___x_2496_);
lean_dec_ref(v___x_2496_);
lean_dec(v_a_2490_);
v___x_2498_ = lean_apply_2(v_mk_2475_, v_a_2476_, v___x_2497_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2498_);
v___x_2500_ = v___x_2492_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_a_2503_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2488_);
v___x_2504_ = l_Lean_Expr_fvarId_x21(v_x_2477_);
v___x_2505_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2504_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2519_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2519_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2519_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2510_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2506_, v_a_2503_);
lean_dec(v_a_2506_);
v___x_2511_ = lean_unsigned_to_nat(1u);
v___x_2512_ = lean_mk_empty_array_with_capacity(v___x_2511_);
v___x_2513_ = lean_array_push(v___x_2512_, v_x_2477_);
v___x_2514_ = lean_expr_abstract(v___x_2510_, v___x_2513_);
lean_dec_ref(v___x_2513_);
lean_dec_ref(v___x_2510_);
v___x_2515_ = lean_apply_2(v_mk_2475_, v_a_2476_, v___x_2514_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2515_);
v___x_2517_ = v___x_2508_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_x_2477_);
lean_dec_ref(v_a_2476_);
lean_dec_ref(v_mk_2475_);
v_a_2520_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2505_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2505_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2477_);
lean_dec_ref(v_a_2476_);
lean_dec_ref(v_mk_2475_);
return v___x_2488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2528_, lean_object* v_b_2529_, lean_object* v___x_2530_, lean_object* v_mk_2531_, lean_object* v_a_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
uint8_t v___x_51502__boxed_2542_; lean_object* v_res_2543_; 
v___x_51502__boxed_2542_ = lean_unbox(v___x_2530_);
v_res_2543_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2528_, v_b_2529_, v___x_51502__boxed_2542_, v_mk_2531_, v_a_2532_, v_x_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v_b_2529_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2544_, lean_object* v_n_2545_, lean_object* v_t_2546_, lean_object* v_b_2547_, uint8_t v_i_2548_, lean_object* v_mk_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
uint8_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = 0;
lean_inc(v_fvars_2544_);
v___x_2559_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2544_, v_t_2546_, v___x_2558_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2559_) == 0)
{
uint8_t v_underBinder_2560_; 
v_underBinder_2560_ = lean_ctor_get_uint8(v_a_2550_, 4);
if (v_underBinder_2560_ == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_n_2545_);
lean_dec(v_fvars_2544_);
v_a_2561_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2563_ = v___x_2559_;
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2559_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = lean_apply_2(v_mk_2549_, v_a_2561_, v_b_2547_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2565_);
v___x_2567_ = v___x_2563_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; 
v_a_2570_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_n(v_a_2570_, 2);
lean_dec_ref(v___x_2559_);
v___x_2571_ = lean_box(v___x_2558_);
v___f_2572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2572_, 0, v_fvars_2544_);
lean_closure_set(v___f_2572_, 1, v_b_2547_);
lean_closure_set(v___f_2572_, 2, v___x_2571_);
lean_closure_set(v___f_2572_, 3, v_mk_2549_);
lean_closure_set(v___f_2572_, 4, v_a_2570_);
v___x_2573_ = 0;
v___x_2574_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2545_, v_i_2548_, v_a_2570_, v___f_2572_, v___x_2573_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2574_;
}
}
else
{
lean_dec_ref(v_mk_2549_);
lean_dec_ref(v_b_2547_);
lean_dec(v_n_2545_);
lean_dec(v_fvars_2544_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2575_, lean_object* v_n_2576_, lean_object* v_t_2577_, lean_object* v_b_2578_, lean_object* v_i_2579_, lean_object* v_mk_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
uint8_t v_i_boxed_2589_; lean_object* v_res_2590_; 
v_i_boxed_2589_ = lean_unbox(v_i_2579_);
v_res_2590_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2575_, v_n_2576_, v_t_2577_, v_b_2578_, v_i_boxed_2589_, v_mk_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2591_, lean_object* v_e_2592_, lean_object* v_topLevel_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
uint8_t v_topLevel_boxed_2602_; lean_object* v_res_2603_; 
v_topLevel_boxed_2602_ = lean_unbox(v_topLevel_2593_);
v_res_2603_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2591_, v_e_2592_, v_topLevel_boxed_2602_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
return v_res_2603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2608_ = lean_unsigned_to_nat(27u);
v___x_2609_ = lean_unsigned_to_nat(1946u);
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2612_ = l_mkPanicMessageWithDecl(v___x_2611_, v___x_2610_, v___x_2609_, v___x_2608_, v___x_2607_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2613_, lean_object* v_fvars_2614_, lean_object* v_b_2615_, uint8_t v___x_2616_, lean_object* v_e_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, uint8_t v_isLet_2620_, uint8_t v_topLevel_2621_, lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
if (v_fst_2613_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_inc_ref(v_x_2622_);
v___x_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_x_2622_);
lean_ctor_set(v___x_2631_, 1, v_fvars_2614_);
v___x_2632_ = lean_expr_instantiate1(v_b_2615_, v_x_2622_);
v___x_2633_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2631_, v___x_2632_, v___x_2616_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2633_) == 0)
{
if (lean_obj_tag(v_e_2617_) == 8)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2669_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2669_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2669_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_declName_2638_; lean_object* v_type_2639_; lean_object* v_value_2640_; lean_object* v_body_2641_; uint8_t v_nondep_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___y_2648_; size_t v___x_2663_; size_t v___x_2664_; uint8_t v___x_2665_; 
v_declName_2638_ = lean_ctor_get(v_e_2617_, 0);
v_type_2639_ = lean_ctor_get(v_e_2617_, 1);
v_value_2640_ = lean_ctor_get(v_e_2617_, 2);
v_body_2641_ = lean_ctor_get(v_e_2617_, 3);
v_nondep_2642_ = lean_ctor_get_uint8(v_e_2617_, sizeof(void*)*4 + 8);
v___x_2643_ = lean_unsigned_to_nat(1u);
v___x_2644_ = lean_mk_empty_array_with_capacity(v___x_2643_);
v___x_2645_ = lean_array_push(v___x_2644_, v_x_2622_);
v___x_2646_ = lean_expr_abstract(v_a_2634_, v___x_2645_);
lean_dec_ref(v___x_2645_);
lean_dec(v_a_2634_);
v___x_2663_ = lean_ptr_addr(v_type_2639_);
v___x_2664_ = lean_ptr_addr(v_a_2618_);
v___x_2665_ = lean_usize_dec_eq(v___x_2663_, v___x_2664_);
if (v___x_2665_ == 0)
{
v___y_2648_ = v___x_2665_;
goto v___jp_2647_;
}
else
{
size_t v___x_2666_; size_t v___x_2667_; uint8_t v___x_2668_; 
v___x_2666_ = lean_ptr_addr(v_value_2640_);
v___x_2667_ = lean_ptr_addr(v_a_2619_);
v___x_2668_ = lean_usize_dec_eq(v___x_2666_, v___x_2667_);
v___y_2648_ = v___x_2668_;
goto v___jp_2647_;
}
v___jp_2647_:
{
if (v___y_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_inc(v_declName_2638_);
lean_dec_ref(v_e_2617_);
v___x_2649_ = l_Lean_Expr_letE___override(v_declName_2638_, v_a_2618_, v_a_2619_, v___x_2646_, v_nondep_2642_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2649_);
v___x_2651_ = v___x_2636_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
else
{
size_t v___x_2653_; size_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = lean_ptr_addr(v_body_2641_);
v___x_2654_ = lean_ptr_addr(v___x_2646_);
v___x_2655_ = lean_usize_dec_eq(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_inc(v_declName_2638_);
lean_dec_ref(v_e_2617_);
v___x_2656_ = l_Lean_Expr_letE___override(v_declName_2638_, v_a_2618_, v_a_2619_, v___x_2646_, v_nondep_2642_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2656_);
v___x_2658_ = v___x_2636_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
else
{
lean_object* v___x_2661_; 
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_a_2619_);
lean_dec_ref(v_a_2618_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v_e_2617_);
v___x_2661_ = v___x_2636_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_e_2617_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
else
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v_x_2622_);
lean_dec_ref(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec_ref(v_e_2617_);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v___x_2633_, 0);
lean_dec(v_unused_2679_);
v___x_2671_ = v___x_2633_;
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v___x_2633_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2674_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2673_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2674_);
v___x_2676_ = v___x_2671_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_dec_ref(v_x_2622_);
lean_dec_ref(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec_ref(v_e_2617_);
return v___x_2633_;
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec_ref(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec_ref(v_e_2617_);
v___x_2680_ = l_Lean_Expr_fvarId_x21(v_x_2622_);
v___x_2681_ = l_Lean_FVarId_getDecl___redArg(v___x_2680_, v___y_2626_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2682_, v_isLet_2620_, v___y_2623_, v___y_2625_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_dec_ref(v___x_2683_);
v___x_2684_ = lean_expr_instantiate1(v_b_2615_, v_x_2622_);
lean_dec_ref(v_x_2622_);
v___x_2685_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2614_, v___x_2684_, v_topLevel_2621_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2685_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref(v_x_2622_);
lean_dec(v_fvars_2614_);
v_a_2686_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2683_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2683_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_x_2622_);
lean_dec(v_fvars_2614_);
v_a_2694_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2681_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2681_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2702_ = _args[0];
lean_object* v_fvars_2703_ = _args[1];
lean_object* v_b_2704_ = _args[2];
lean_object* v___x_2705_ = _args[3];
lean_object* v_e_2706_ = _args[4];
lean_object* v_a_2707_ = _args[5];
lean_object* v_a_2708_ = _args[6];
lean_object* v_isLet_2709_ = _args[7];
lean_object* v_topLevel_2710_ = _args[8];
lean_object* v_x_2711_ = _args[9];
lean_object* v___y_2712_ = _args[10];
lean_object* v___y_2713_ = _args[11];
lean_object* v___y_2714_ = _args[12];
lean_object* v___y_2715_ = _args[13];
lean_object* v___y_2716_ = _args[14];
lean_object* v___y_2717_ = _args[15];
lean_object* v___y_2718_ = _args[16];
lean_object* v___y_2719_ = _args[17];
_start:
{
uint8_t v_fst_51647__boxed_2720_; uint8_t v___x_51648__boxed_2721_; uint8_t v_isLet_boxed_2722_; uint8_t v_topLevel_boxed_2723_; lean_object* v_res_2724_; 
v_fst_51647__boxed_2720_ = lean_unbox(v_fst_2702_);
v___x_51648__boxed_2721_ = lean_unbox(v___x_2705_);
v_isLet_boxed_2722_ = lean_unbox(v_isLet_2709_);
v_topLevel_boxed_2723_ = lean_unbox(v_topLevel_2710_);
v_res_2724_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_51647__boxed_2720_, v_fvars_2703_, v_b_2704_, v___x_51648__boxed_2721_, v_e_2706_, v_a_2707_, v_a_2708_, v_isLet_boxed_2722_, v_topLevel_boxed_2723_, v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec_ref(v_b_2704_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2725_, lean_object* v_e_2726_, uint8_t v_isLet_2727_, lean_object* v_n_2728_, lean_object* v_t_2729_, lean_object* v_v_2730_, lean_object* v_b_2731_, uint8_t v_topLevel_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = 0;
lean_inc(v_fvars_2725_);
v___x_2756_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2725_, v_t_2729_, v___x_2755_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2875_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2875_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2875_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; 
lean_inc(v_fvars_2725_);
v___x_2761_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2725_, v_v_2730_, v___x_2755_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2874_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2874_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2874_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; uint8_t v___y_2770_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; uint8_t v_descend_2814_; uint8_t v_underBinder_2815_; uint8_t v_usedOnly_2816_; uint8_t v_merge_2817_; uint8_t v_lift_2818_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; uint8_t v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; uint8_t v___y_2856_; 
v_descend_2814_ = lean_ctor_get_uint8(v_a_2733_, 3);
v_underBinder_2815_ = lean_ctor_get_uint8(v_a_2733_, 4);
v_usedOnly_2816_ = lean_ctor_get_uint8(v_a_2733_, 5);
v_merge_2817_ = lean_ctor_get_uint8(v_a_2733_, 6);
v_lift_2818_ = lean_ctor_get_uint8(v_a_2733_, 10);
if (v_usedOnly_2816_ == 0)
{
v___y_2856_ = v___x_2755_;
goto v___jp_2855_;
}
else
{
uint8_t v___x_2872_; 
v___x_2872_ = l_Lean_Expr_hasLooseBVars(v_b_2731_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_del_object(v___x_2764_);
lean_dec(v_a_2762_);
lean_del_object(v___x_2759_);
lean_dec(v_a_2757_);
lean_dec(v_n_2728_);
lean_dec_ref(v_e_2726_);
v___x_2873_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2725_, v_b_2731_, v_topLevel_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
return v___x_2873_;
}
else
{
v___y_2856_ = v___x_2755_;
goto v___jp_2855_;
}
}
v___jp_2766_:
{
if (v___y_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
lean_dec_ref(v___y_2767_);
lean_dec_ref(v_e_2726_);
v___x_2771_ = l_Lean_Expr_letE___override(v___y_2768_, v_a_2757_, v_a_2762_, v_b_2731_, v___y_2769_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2771_);
v___x_2773_ = v___x_2764_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
else
{
size_t v___x_2775_; size_t v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = lean_ptr_addr(v___y_2767_);
lean_dec_ref(v___y_2767_);
v___x_2776_ = lean_ptr_addr(v_b_2731_);
v___x_2777_ = lean_usize_dec_eq(v___x_2775_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_dec_ref(v_e_2726_);
v___x_2778_ = l_Lean_Expr_letE___override(v___y_2768_, v_a_2757_, v_a_2762_, v_b_2731_, v___y_2769_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2778_);
v___x_2780_ = v___x_2764_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
else
{
lean_object* v___x_2783_; 
lean_dec(v___y_2768_);
lean_dec(v_a_2762_);
lean_dec(v_a_2757_);
lean_dec_ref(v_b_2731_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_e_2726_);
v___x_2783_ = v___x_2764_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_e_2726_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
v___jp_2785_:
{
if (lean_obj_tag(v_e_2726_) == 8)
{
lean_object* v_declName_2786_; lean_object* v_type_2787_; lean_object* v_value_2788_; lean_object* v_body_2789_; uint8_t v_nondep_2790_; size_t v___x_2791_; size_t v___x_2792_; uint8_t v___x_2793_; 
lean_del_object(v___x_2759_);
v_declName_2786_ = lean_ctor_get(v_e_2726_, 0);
v_type_2787_ = lean_ctor_get(v_e_2726_, 1);
v_value_2788_ = lean_ctor_get(v_e_2726_, 2);
v_body_2789_ = lean_ctor_get(v_e_2726_, 3);
v_nondep_2790_ = lean_ctor_get_uint8(v_e_2726_, sizeof(void*)*4 + 8);
v___x_2791_ = lean_ptr_addr(v_type_2787_);
v___x_2792_ = lean_ptr_addr(v_a_2757_);
v___x_2793_ = lean_usize_dec_eq(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_inc(v_declName_2786_);
lean_inc_ref(v_body_2789_);
v___y_2767_ = v_body_2789_;
v___y_2768_ = v_declName_2786_;
v___y_2769_ = v_nondep_2790_;
v___y_2770_ = v___x_2793_;
goto v___jp_2766_;
}
else
{
size_t v___x_2794_; size_t v___x_2795_; uint8_t v___x_2796_; 
v___x_2794_ = lean_ptr_addr(v_value_2788_);
v___x_2795_ = lean_ptr_addr(v_a_2762_);
v___x_2796_ = lean_usize_dec_eq(v___x_2794_, v___x_2795_);
lean_inc(v_declName_2786_);
lean_inc_ref(v_body_2789_);
v___y_2767_ = v_body_2789_;
v___y_2768_ = v_declName_2786_;
v___y_2769_ = v_nondep_2790_;
v___y_2770_ = v___x_2796_;
goto v___jp_2766_;
}
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
lean_del_object(v___x_2764_);
lean_dec(v_a_2762_);
lean_dec(v_a_2757_);
lean_dec_ref(v_b_2731_);
lean_dec_ref(v_e_2726_);
v___x_2797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2798_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2797_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2798_);
v___x_2800_ = v___x_2759_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
v___jp_2802_:
{
uint8_t v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = 0;
v___x_2813_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2804_, v_a_2757_, v_a_2762_, v___y_2807_, v___x_2755_, v___x_2812_, v___y_2803_, v___y_2806_, v___y_2805_, v___y_2811_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2813_;
}
v___jp_2819_:
{
if (v_underBinder_2815_ == 0)
{
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2821_);
goto v___jp_2785_;
}
else
{
if (v_descend_2814_ == 0)
{
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2821_);
goto v___jp_2785_;
}
else
{
lean_del_object(v___x_2764_);
lean_del_object(v___x_2759_);
lean_dec_ref(v_b_2731_);
lean_dec_ref(v_e_2726_);
v___y_2803_ = v___y_2820_;
v___y_2804_ = v___y_2821_;
v___y_2805_ = v___y_2823_;
v___y_2806_ = v___y_2822_;
v___y_2807_ = v___y_2824_;
v___y_2808_ = v___y_2825_;
v___y_2809_ = v___y_2826_;
v___y_2810_ = v___y_2828_;
v___y_2811_ = v___y_2827_;
goto v___jp_2802_;
}
}
}
v___jp_2829_:
{
lean_object* v___x_2838_; 
lean_inc(v_a_2762_);
lean_inc(v_a_2757_);
v___x_2838_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2725_, v_n_2728_, v_a_2757_, v_a_2762_, v___y_2831_, v___y_2833_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v_fst_2840_; lean_object* v_snd_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___f_2845_; uint8_t v___x_2846_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref(v___x_2838_);
v_fst_2840_ = lean_ctor_get(v_a_2839_, 0);
lean_inc_n(v_fst_2840_, 2);
v_snd_2841_ = lean_ctor_get(v_a_2839_, 1);
lean_inc(v_snd_2841_);
lean_dec(v_a_2839_);
v___x_2842_ = lean_box(v___x_2755_);
v___x_2843_ = lean_box(v_isLet_2727_);
v___x_2844_ = lean_box(v_topLevel_2732_);
lean_inc(v_a_2762_);
lean_inc(v_a_2757_);
lean_inc_ref(v_e_2726_);
lean_inc_ref(v_b_2731_);
v___f_2845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2845_, 0, v_fst_2840_);
lean_closure_set(v___f_2845_, 1, v_fvars_2725_);
lean_closure_set(v___f_2845_, 2, v_b_2731_);
lean_closure_set(v___f_2845_, 3, v___x_2842_);
lean_closure_set(v___f_2845_, 4, v_e_2726_);
lean_closure_set(v___f_2845_, 5, v_a_2757_);
lean_closure_set(v___f_2845_, 6, v_a_2762_);
lean_closure_set(v___f_2845_, 7, v___x_2843_);
lean_closure_set(v___f_2845_, 8, v___x_2844_);
v___x_2846_ = lean_unbox(v_fst_2840_);
lean_dec(v_fst_2840_);
if (v___x_2846_ == 0)
{
v___y_2820_ = v___y_2831_;
v___y_2821_ = v_snd_2841_;
v___y_2822_ = v___y_2832_;
v___y_2823_ = v___y_2833_;
v___y_2824_ = v___f_2845_;
v___y_2825_ = v___y_2835_;
v___y_2826_ = v___y_2836_;
v___y_2827_ = v___y_2834_;
v___y_2828_ = v___y_2837_;
goto v___jp_2819_;
}
else
{
if (v___y_2830_ == 0)
{
lean_del_object(v___x_2764_);
lean_del_object(v___x_2759_);
lean_dec_ref(v_b_2731_);
lean_dec_ref(v_e_2726_);
v___y_2803_ = v___y_2831_;
v___y_2804_ = v_snd_2841_;
v___y_2805_ = v___y_2833_;
v___y_2806_ = v___y_2832_;
v___y_2807_ = v___f_2845_;
v___y_2808_ = v___y_2835_;
v___y_2809_ = v___y_2836_;
v___y_2810_ = v___y_2837_;
v___y_2811_ = v___y_2834_;
goto v___jp_2802_;
}
else
{
v___y_2820_ = v___y_2831_;
v___y_2821_ = v_snd_2841_;
v___y_2822_ = v___y_2832_;
v___y_2823_ = v___y_2833_;
v___y_2824_ = v___f_2845_;
v___y_2825_ = v___y_2835_;
v___y_2826_ = v___y_2836_;
v___y_2827_ = v___y_2834_;
v___y_2828_ = v___y_2837_;
goto v___jp_2819_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_del_object(v___x_2764_);
lean_dec(v_a_2762_);
lean_del_object(v___x_2759_);
lean_dec(v_a_2757_);
lean_dec_ref(v_b_2731_);
lean_dec_ref(v_e_2726_);
lean_dec(v_fvars_2725_);
v_a_2847_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2838_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2838_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
v___jp_2855_:
{
if (v_merge_2817_ == 0)
{
v___y_2830_ = v___y_2856_;
v___y_2831_ = v_a_2733_;
v___y_2832_ = v_a_2734_;
v___y_2833_ = v_a_2735_;
v___y_2834_ = v_a_2736_;
v___y_2835_ = v_a_2737_;
v___y_2836_ = v_a_2738_;
v___y_2837_ = v_a_2739_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2857_; lean_object* v_valueMap_2858_; lean_object* v___x_2859_; 
v___x_2857_ = lean_st_ref_get(v_a_2735_);
v_valueMap_2858_ = lean_ctor_get(v___x_2857_, 2);
lean_inc_ref(v_valueMap_2858_);
lean_dec(v___x_2857_);
v___x_2859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2858_, v_a_2762_);
lean_dec_ref(v_valueMap_2858_);
if (lean_obj_tag(v___x_2859_) == 1)
{
lean_del_object(v___x_2764_);
lean_dec(v_a_2762_);
lean_del_object(v___x_2759_);
lean_dec(v_a_2757_);
lean_dec(v_n_2728_);
lean_dec_ref(v_e_2726_);
if (v_isLet_2727_ == 0)
{
lean_object* v_val_2860_; 
v_val_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_val_2860_);
lean_dec_ref(v___x_2859_);
v___y_2742_ = v_val_2860_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
v___y_2749_ = v_a_2739_;
goto v___jp_2741_;
}
else
{
if (v_lift_2818_ == 0)
{
lean_object* v_val_2861_; 
v_val_2861_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_val_2861_);
lean_dec_ref(v___x_2859_);
v___y_2742_ = v_val_2861_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
v___y_2749_ = v_a_2739_;
goto v___jp_2741_;
}
else
{
lean_object* v_val_2862_; lean_object* v___x_2863_; 
v_val_2862_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_val_2862_);
lean_dec_ref(v___x_2859_);
v___x_2863_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2862_, v_a_2735_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_dec_ref(v___x_2863_);
v___y_2742_ = v_val_2862_;
v___y_2743_ = v_a_2733_;
v___y_2744_ = v_a_2734_;
v___y_2745_ = v_a_2735_;
v___y_2746_ = v_a_2736_;
v___y_2747_ = v_a_2737_;
v___y_2748_ = v_a_2738_;
v___y_2749_ = v_a_2739_;
goto v___jp_2741_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_val_2862_);
lean_dec_ref(v_b_2731_);
lean_dec(v_fvars_2725_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
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
}
}
else
{
lean_dec(v___x_2859_);
v___y_2830_ = v___y_2856_;
v___y_2831_ = v_a_2733_;
v___y_2832_ = v_a_2734_;
v___y_2833_ = v_a_2735_;
v___y_2834_ = v_a_2736_;
v___y_2835_ = v_a_2737_;
v___y_2836_ = v_a_2738_;
v___y_2837_ = v_a_2739_;
goto v___jp_2829_;
}
}
}
}
}
else
{
lean_del_object(v___x_2759_);
lean_dec(v_a_2757_);
lean_dec_ref(v_b_2731_);
lean_dec(v_n_2728_);
lean_dec_ref(v_e_2726_);
lean_dec(v_fvars_2725_);
return v___x_2761_;
}
}
}
else
{
lean_dec_ref(v_b_2731_);
lean_dec_ref(v_v_2730_);
lean_dec(v_n_2728_);
lean_dec_ref(v_e_2726_);
lean_dec(v_fvars_2725_);
return v___x_2756_;
}
v___jp_2741_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_inc(v___y_2742_);
v___x_2750_ = l_Lean_Expr_fvar___override(v___y_2742_);
v___x_2751_ = lean_expr_instantiate1(v_b_2731_, v___x_2750_);
lean_dec_ref(v___x_2750_);
lean_dec_ref(v_b_2731_);
v___x_2752_ = lean_box(v_topLevel_2732_);
v___x_2753_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2753_, 0, v_fvars_2725_);
lean_closure_set(v___x_2753_, 1, v___x_2751_);
lean_closure_set(v___x_2753_, 2, v___x_2752_);
v___x_2754_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2742_, v___x_2753_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2876_, lean_object* v_struct_2877_, lean_object* v___y_2878_, lean_object* v_typeName_2879_, lean_object* v_idx_2880_, lean_object* v_e_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
uint8_t v___y_51423__boxed_2890_; lean_object* v_res_2891_; 
v___y_51423__boxed_2890_ = lean_unbox(v___y_2878_);
v_res_2891_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2876_, v_struct_2877_, v___y_51423__boxed_2890_, v_typeName_2879_, v_idx_2880_, v_e_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2891_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2895_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2896_ = lean_unsigned_to_nat(75u);
v___x_2897_ = lean_unsigned_to_nat(229u);
v___x_2898_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2899_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2900_ = l_mkPanicMessageWithDecl(v___x_2899_, v___x_2898_, v___x_2897_, v___x_2896_, v___x_2895_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2901_, lean_object* v_e_2902_, lean_object* v_fvars_2903_, uint8_t v___x_2904_, uint8_t v_topLevel_2905_, uint8_t v___y_2906_, lean_object* v_____r_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_k_2917_; 
switch(lean_obj_tag(v_e_2902_))
{
case 5:
{
lean_object* v___x_2920_; lean_object* v_dummy_2921_; lean_object* v_nargs_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2920_ = l_Lean_Expr_getAppFn(v_e_2902_);
v_dummy_2921_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2922_ = l_Lean_Expr_getAppNumArgs(v_e_2902_);
lean_inc(v_nargs_2922_);
v___x_2923_ = lean_mk_array(v_nargs_2922_, v_dummy_2921_);
v___x_2924_ = lean_unsigned_to_nat(1u);
v___x_2925_ = lean_nat_sub(v_nargs_2922_, v___x_2924_);
lean_dec(v_nargs_2922_);
lean_inc_ref(v_e_2902_);
v___x_2926_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2902_, v___x_2923_, v___x_2925_);
v___x_2927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2927_, 0, v_fvars_2903_);
lean_closure_set(v___x_2927_, 1, v___x_2920_);
lean_closure_set(v___x_2927_, 2, v___x_2926_);
v_k_2917_ = v___x_2927_;
goto v___jp_2916_;
}
case 6:
{
lean_object* v_binderName_2928_; lean_object* v_binderType_2929_; lean_object* v_body_2930_; uint8_t v_binderInfo_2931_; lean_object* v___x_2932_; lean_object* v___f_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_binderName_2928_ = lean_ctor_get(v_e_2902_, 0);
v_binderType_2929_ = lean_ctor_get(v_e_2902_, 1);
v_body_2930_ = lean_ctor_get(v_e_2902_, 2);
v_binderInfo_2931_ = lean_ctor_get_uint8(v_e_2902_, sizeof(void*)*3 + 8);
v___x_2932_ = lean_box(v_binderInfo_2931_);
lean_inc_ref_n(v_body_2930_, 2);
lean_inc_ref_n(v_binderType_2929_, 2);
lean_inc_ref(v_e_2902_);
lean_inc_n(v_binderName_2928_, 2);
v___f_2933_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2933_, 0, v_binderName_2928_);
lean_closure_set(v___f_2933_, 1, v___x_2932_);
lean_closure_set(v___f_2933_, 2, v_e_2902_);
lean_closure_set(v___f_2933_, 3, v_binderType_2929_);
lean_closure_set(v___f_2933_, 4, v_body_2930_);
v___x_2934_ = lean_box(v_binderInfo_2931_);
v___x_2935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2935_, 0, v_fvars_2903_);
lean_closure_set(v___x_2935_, 1, v_binderName_2928_);
lean_closure_set(v___x_2935_, 2, v_binderType_2929_);
lean_closure_set(v___x_2935_, 3, v_body_2930_);
lean_closure_set(v___x_2935_, 4, v___x_2934_);
lean_closure_set(v___x_2935_, 5, v___f_2933_);
v_k_2917_ = v___x_2935_;
goto v___jp_2916_;
}
case 7:
{
lean_object* v_binderName_2936_; lean_object* v_binderType_2937_; lean_object* v_body_2938_; uint8_t v_binderInfo_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_binderName_2936_ = lean_ctor_get(v_e_2902_, 0);
v_binderType_2937_ = lean_ctor_get(v_e_2902_, 1);
v_body_2938_ = lean_ctor_get(v_e_2902_, 2);
v_binderInfo_2939_ = lean_ctor_get_uint8(v_e_2902_, sizeof(void*)*3 + 8);
v___x_2940_ = lean_box(v_binderInfo_2939_);
lean_inc_ref_n(v_body_2938_, 2);
lean_inc_ref_n(v_binderType_2937_, 2);
lean_inc_ref(v_e_2902_);
lean_inc_n(v_binderName_2936_, 2);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2941_, 0, v_binderName_2936_);
lean_closure_set(v___f_2941_, 1, v___x_2940_);
lean_closure_set(v___f_2941_, 2, v_e_2902_);
lean_closure_set(v___f_2941_, 3, v_binderType_2937_);
lean_closure_set(v___f_2941_, 4, v_body_2938_);
v___x_2942_ = lean_box(v_binderInfo_2939_);
v___x_2943_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2943_, 0, v_fvars_2903_);
lean_closure_set(v___x_2943_, 1, v_binderName_2936_);
lean_closure_set(v___x_2943_, 2, v_binderType_2937_);
lean_closure_set(v___x_2943_, 3, v_body_2938_);
lean_closure_set(v___x_2943_, 4, v___x_2942_);
lean_closure_set(v___x_2943_, 5, v___f_2941_);
v_k_2917_ = v___x_2943_;
goto v___jp_2916_;
}
case 8:
{
uint8_t v_nondep_2944_; 
v_nondep_2944_ = lean_ctor_get_uint8(v_e_2902_, sizeof(void*)*4 + 8);
if (v_nondep_2944_ == 0)
{
lean_object* v_declName_2945_; lean_object* v_type_2946_; lean_object* v_value_2947_; lean_object* v_body_2948_; lean_object* v___x_2949_; 
v_declName_2945_ = lean_ctor_get(v_e_2902_, 0);
lean_inc(v_declName_2945_);
v_type_2946_ = lean_ctor_get(v_e_2902_, 1);
lean_inc_ref(v_type_2946_);
v_value_2947_ = lean_ctor_get(v_e_2902_, 2);
lean_inc_ref(v_value_2947_);
v_body_2948_ = lean_ctor_get(v_e_2902_, 3);
lean_inc_ref(v_body_2948_);
v___x_2949_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2903_, v_e_2902_, v___x_2904_, v_declName_2945_, v_type_2946_, v_value_2947_, v_body_2948_, v_topLevel_2905_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_2949_;
}
else
{
lean_object* v_declName_2950_; lean_object* v_type_2951_; lean_object* v_value_2952_; lean_object* v_body_2953_; lean_object* v___x_2954_; 
v_declName_2950_ = lean_ctor_get(v_e_2902_, 0);
lean_inc(v_declName_2950_);
v_type_2951_ = lean_ctor_get(v_e_2902_, 1);
lean_inc_ref(v_type_2951_);
v_value_2952_ = lean_ctor_get(v_e_2902_, 2);
lean_inc_ref(v_value_2952_);
v_body_2953_ = lean_ctor_get(v_e_2902_, 3);
lean_inc_ref(v_body_2953_);
v___x_2954_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2903_, v_e_2902_, v___y_2906_, v_declName_2950_, v_type_2951_, v_value_2952_, v_body_2953_, v_topLevel_2905_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_2954_;
}
}
case 10:
{
lean_object* v_data_2955_; lean_object* v_expr_2956_; lean_object* v___x_2957_; 
v_data_2955_ = lean_ctor_get(v_e_2902_, 0);
v_expr_2956_ = lean_ctor_get(v_e_2902_, 1);
lean_inc_ref(v_expr_2956_);
v___x_2957_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2903_, v_expr_2956_, v_topLevel_2905_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2972_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2972_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2972_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
size_t v___x_2962_; size_t v___x_2963_; uint8_t v___x_2964_; 
v___x_2962_ = lean_ptr_addr(v_expr_2956_);
v___x_2963_ = lean_ptr_addr(v_a_2958_);
v___x_2964_ = lean_usize_dec_eq(v___x_2962_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
lean_inc(v_data_2955_);
lean_dec_ref(v_e_2902_);
v___x_2965_ = l_Lean_Expr_mdata___override(v_data_2955_, v_a_2958_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2965_);
v___x_2967_ = v___x_2960_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
else
{
lean_object* v___x_2970_; 
lean_dec(v_a_2958_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v_e_2902_);
v___x_2970_ = v___x_2960_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_e_2902_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_dec_ref(v_e_2902_);
return v___x_2957_;
}
}
case 11:
{
lean_object* v_typeName_2973_; lean_object* v_idx_2974_; lean_object* v_struct_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; 
v_typeName_2973_ = lean_ctor_get(v_e_2902_, 0);
v_idx_2974_ = lean_ctor_get(v_e_2902_, 1);
v_struct_2975_ = lean_ctor_get(v_e_2902_, 2);
v___x_2976_ = lean_box(v___y_2906_);
lean_inc_ref(v_e_2902_);
lean_inc(v_idx_2974_);
lean_inc(v_typeName_2973_);
lean_inc_ref(v_struct_2975_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2977_, 0, v_fvars_2903_);
lean_closure_set(v___f_2977_, 1, v_struct_2975_);
lean_closure_set(v___f_2977_, 2, v___x_2976_);
lean_closure_set(v___f_2977_, 3, v_typeName_2973_);
lean_closure_set(v___f_2977_, 4, v_idx_2974_);
lean_closure_set(v___f_2977_, 5, v_e_2902_);
v_k_2917_ = v___f_2977_;
goto v___jp_2916_;
}
default: 
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec(v_fvars_2903_);
lean_dec_ref(v_e_2902_);
v___x_2978_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2979_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2978_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_2979_;
}
}
v___jp_2916_:
{
if (v_descend_2901_ == 0)
{
lean_object* v___x_2918_; 
lean_dec_ref(v_k_2917_);
v___x_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_e_2902_);
return v___x_2918_;
}
else
{
lean_object* v___x_2919_; 
lean_dec_ref(v_e_2902_);
lean_inc(v___y_2914_);
lean_inc_ref(v___y_2913_);
lean_inc(v___y_2912_);
lean_inc_ref(v___y_2911_);
lean_inc(v___y_2910_);
lean_inc(v___y_2909_);
lean_inc_ref(v___y_2908_);
v___x_2919_ = lean_apply_8(v_k_2917_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, lean_box(0));
return v___x_2919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2980_, lean_object* v_e_2981_, lean_object* v_fvars_2982_, lean_object* v___x_2983_, lean_object* v_topLevel_2984_, lean_object* v___y_2985_, lean_object* v_____r_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
uint8_t v_descend_boxed_2995_; uint8_t v___x_51576__boxed_2996_; uint8_t v_topLevel_boxed_2997_; uint8_t v___y_51577__boxed_2998_; lean_object* v_res_2999_; 
v_descend_boxed_2995_ = lean_unbox(v_descend_2980_);
v___x_51576__boxed_2996_ = lean_unbox(v___x_2983_);
v_topLevel_boxed_2997_ = lean_unbox(v_topLevel_2984_);
v___y_51577__boxed_2998_ = lean_unbox(v___y_2985_);
v_res_2999_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2995_, v_e_2981_, v_fvars_2982_, v___x_51576__boxed_2996_, v_topLevel_boxed_2997_, v___y_51577__boxed_2998_, v_____r_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_3000_, lean_object* v_e_3001_, uint8_t v_topLevel_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___y_3012_; lean_object* v_a_3013_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3023_; lean_object* v___y_3024_; uint8_t v___x_3027_; 
v___x_3027_ = l_Lean_Expr_isAtomic(v_e_3001_);
if (v___x_3027_ == 0)
{
uint8_t v_proofs_3028_; uint8_t v_types_3029_; uint8_t v_descend_3030_; lean_object* v___y_3032_; lean_object* v___y_3033_; uint8_t v___y_3050_; 
v_proofs_3028_ = lean_ctor_get_uint8(v_a_3003_, 0);
v_types_3029_ = lean_ctor_get_uint8(v_a_3003_, 1);
v_descend_3030_ = lean_ctor_get_uint8(v_a_3003_, 3);
if (v_descend_3030_ == 0)
{
goto v___jp_3073_;
}
else
{
if (v___x_3027_ == 0)
{
v___y_3050_ = v___x_3027_;
goto v___jp_3049_;
}
else
{
goto v___jp_3073_;
}
}
v___jp_3031_:
{
if (v_proofs_3028_ == 0)
{
lean_object* v___x_3034_; 
lean_inc_ref(v_e_3001_);
v___x_3034_ = l_Lean_Meta_isProof(v_e_3001_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; uint8_t v___x_3036_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
v___x_3036_ = lean_unbox(v_a_3035_);
lean_dec(v_a_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec_ref(v_e_3001_);
v___x_3037_ = lean_box(0);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
v___x_3038_ = lean_apply_9(v___y_3032_, v___x_3037_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, lean_box(0));
v___y_3019_ = v___y_3033_;
v___y_3020_ = v___x_3038_;
goto v___jp_3018_;
}
else
{
lean_dec_ref(v___y_3032_);
v___y_3012_ = v___y_3033_;
v_a_3013_ = v_e_3001_;
goto v___jp_3011_;
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v_e_3001_);
v_a_3039_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3034_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3034_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v_e_3001_);
v___x_3047_ = lean_box(0);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
v___x_3048_ = lean_apply_9(v___y_3032_, v___x_3047_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, lean_box(0));
v___y_3019_ = v___y_3033_;
v___y_3020_ = v___x_3048_;
goto v___jp_3018_;
}
}
v___jp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3051_ = lean_st_ref_get(v_a_3004_);
v___x_3052_ = lean_box(v_topLevel_3002_);
lean_inc_ref(v_e_3001_);
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v_e_3001_);
v___x_3054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3051_, v___x_3053_);
lean_dec(v___x_3051_);
if (lean_obj_tag(v___x_3054_) == 0)
{
uint8_t v___x_3055_; 
v___x_3055_ = l_Lean_Meta_ExtractLets_containsLet(v_e_3001_);
if (v___x_3055_ == 0)
{
lean_dec(v_fvars_3000_);
v___y_3012_ = v___x_3053_;
v_a_3013_ = v_e_3001_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v___f_3062_; 
v___x_3056_ = lean_box(v_descend_3030_);
v___x_3057_ = lean_box(v___x_3055_);
v___x_3058_ = lean_box(v_topLevel_3002_);
v___x_3059_ = lean_box(v___y_3050_);
lean_inc_ref_n(v_e_3001_, 2);
v___f_3060_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3060_, 0, v___x_3056_);
lean_closure_set(v___f_3060_, 1, v_e_3001_);
lean_closure_set(v___f_3060_, 2, v_fvars_3000_);
lean_closure_set(v___f_3060_, 3, v___x_3057_);
lean_closure_set(v___f_3060_, 4, v___x_3058_);
lean_closure_set(v___f_3060_, 5, v___x_3059_);
v___x_3061_ = lean_box(v_types_3029_);
lean_inc_ref(v___f_3060_);
v___f_3062_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3062_, 0, v___x_3061_);
lean_closure_set(v___f_3062_, 1, v_e_3001_);
lean_closure_set(v___f_3062_, 2, v___f_3060_);
if (v_topLevel_3002_ == 0)
{
lean_dec_ref(v___f_3060_);
v___y_3032_ = v___f_3062_;
v___y_3033_ = v___x_3053_;
goto v___jp_3031_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_Expr_isLet(v_e_3001_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
v___x_3064_ = l_Lean_Expr_isMData(v_e_3001_);
if (v___x_3064_ == 0)
{
lean_dec_ref(v___f_3060_);
v___y_3032_ = v___f_3062_;
v___y_3033_ = v___x_3053_;
goto v___jp_3031_;
}
else
{
lean_dec_ref(v___f_3062_);
lean_dec_ref(v_e_3001_);
v___y_3023_ = v___f_3060_;
v___y_3024_ = v___x_3053_;
goto v___jp_3022_;
}
}
else
{
lean_dec_ref(v___f_3062_);
lean_dec_ref(v_e_3001_);
v___y_3023_ = v___f_3060_;
v___y_3024_ = v___x_3053_;
goto v___jp_3022_;
}
}
}
}
else
{
lean_object* v_val_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref(v___x_3053_);
lean_dec_ref(v_e_3001_);
lean_dec(v_fvars_3000_);
v_val_3065_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3054_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_val_3065_);
lean_dec(v___x_3054_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 0);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_val_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
v___jp_3073_:
{
if (v_topLevel_3002_ == 0)
{
lean_object* v___x_3074_; 
lean_dec(v_fvars_3000_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_e_3001_);
return v___x_3074_;
}
else
{
if (v___x_3027_ == 0)
{
v___y_3050_ = v___x_3027_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3075_; 
lean_dec(v_fvars_3000_);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v_e_3001_);
return v___x_3075_;
}
}
}
}
else
{
lean_object* v___x_3076_; 
lean_dec(v_fvars_3000_);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_e_3001_);
return v___x_3076_;
}
v___jp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3014_ = lean_st_ref_take(v_a_3004_);
lean_inc_ref(v_a_3013_);
v___x_3015_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3014_, v___y_3012_, v_a_3013_);
v___x_3016_ = lean_st_ref_set(v_a_3004_, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_a_3013_);
return v___x_3017_;
}
v___jp_3018_:
{
if (lean_obj_tag(v___y_3020_) == 0)
{
lean_object* v_a_3021_; 
v_a_3021_ = lean_ctor_get(v___y_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___y_3020_);
v___y_3012_ = v___y_3019_;
v_a_3013_ = v_a_3021_;
goto v___jp_3011_;
}
else
{
lean_dec_ref(v___y_3019_);
return v___y_3020_;
}
}
v___jp_3022_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_box(0);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
v___x_3026_ = lean_apply_9(v___y_3023_, v___x_3025_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, lean_box(0));
v___y_3019_ = v___y_3024_;
v___y_3020_ = v___x_3026_;
goto v___jp_3018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3077_, lean_object* v_struct_3078_, uint8_t v___y_3079_, lean_object* v_typeName_3080_, lean_object* v_idx_3081_, lean_object* v_e_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v___x_3091_; 
lean_inc_ref(v_struct_3078_);
v___x_3091_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3077_, v_struct_3078_, v___y_3079_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3106_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3106_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3106_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
size_t v___x_3096_; size_t v___x_3097_; uint8_t v___x_3098_; 
v___x_3096_ = lean_ptr_addr(v_struct_3078_);
lean_dec_ref(v_struct_3078_);
v___x_3097_ = lean_ptr_addr(v_a_3092_);
v___x_3098_ = lean_usize_dec_eq(v___x_3096_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_dec_ref(v_e_3082_);
v___x_3099_ = l_Lean_Expr_proj___override(v_typeName_3080_, v_idx_3081_, v_a_3092_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3099_);
v___x_3101_ = v___x_3094_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
else
{
lean_object* v___x_3104_; 
lean_dec(v_a_3092_);
lean_dec(v_idx_3081_);
lean_dec(v_typeName_3080_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v_e_3082_);
v___x_3104_ = v___x_3094_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_e_3082_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_dec_ref(v_e_3082_);
lean_dec(v_idx_3081_);
lean_dec(v_typeName_3080_);
lean_dec_ref(v_struct_3078_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3107_, lean_object* v_sz_3108_, lean_object* v_i_3109_, lean_object* v_bs_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
size_t v_sz_boxed_3119_; size_t v_i_boxed_3120_; lean_object* v_res_3121_; 
v_sz_boxed_3119_ = lean_unbox_usize(v_sz_3108_);
lean_dec(v_sz_3108_);
v_i_boxed_3120_ = lean_unbox_usize(v_i_3109_);
lean_dec(v_i_3109_);
v_res_3121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3107_, v_sz_boxed_3119_, v_i_boxed_3120_, v_bs_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3122_, lean_object* v_fst_3123_, lean_object* v_fvars_3124_, lean_object* v_a_3125_, lean_object* v_b_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3122_, v_fst_3123_, v_fvars_3124_, v_a_3125_, v_b_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v_fst_3123_);
lean_dec(v_upperBound_3122_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3136_, lean_object* v_e_3137_, lean_object* v_isLet_3138_, lean_object* v_n_3139_, lean_object* v_t_3140_, lean_object* v_v_3141_, lean_object* v_b_3142_, lean_object* v_topLevel_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
uint8_t v_isLet_boxed_3152_; uint8_t v_topLevel_boxed_3153_; lean_object* v_res_3154_; 
v_isLet_boxed_3152_ = lean_unbox(v_isLet_3138_);
v_topLevel_boxed_3153_ = lean_unbox(v_topLevel_3143_);
v_res_3154_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3136_, v_e_3137_, v_isLet_boxed_3152_, v_n_3139_, v_t_3140_, v_v_3141_, v_b_3142_, v_topLevel_boxed_3153_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3155_, lean_object* v_name_3156_, lean_object* v_type_3157_, lean_object* v_val_3158_, lean_object* v_k_3159_, uint8_t v_nondep_3160_, uint8_t v_kind_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3156_, v_type_3157_, v_val_3158_, v_k_3159_, v_nondep_3160_, v_kind_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3171_, lean_object* v_name_3172_, lean_object* v_type_3173_, lean_object* v_val_3174_, lean_object* v_k_3175_, lean_object* v_nondep_3176_, lean_object* v_kind_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_nondep_boxed_3186_; uint8_t v_kind_boxed_3187_; lean_object* v_res_3188_; 
v_nondep_boxed_3186_ = lean_unbox(v_nondep_3176_);
v_kind_boxed_3187_ = lean_unbox(v_kind_3177_);
v_res_3188_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3171_, v_name_3172_, v_type_3173_, v_val_3174_, v_k_3175_, v_nondep_boxed_3186_, v_kind_boxed_3187_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3189_, lean_object* v_m_3190_, lean_object* v_a_3191_, lean_object* v_b_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3190_, v_a_3191_, v_b_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3194_, lean_object* v_m_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3195_, v_a_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3198_, lean_object* v_m_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3198_, v_m_3199_, v_a_3200_);
lean_dec_ref(v_a_3200_);
lean_dec_ref(v_m_3199_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3202_, lean_object* v_fst_3203_, lean_object* v_fvars_3204_, lean_object* v_inst_3205_, lean_object* v_R_3206_, lean_object* v_a_3207_, lean_object* v_b_3208_, lean_object* v_c_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3202_, v_fst_3203_, v_fvars_3204_, v_a_3207_, v_b_3208_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3219_, lean_object* v_fst_3220_, lean_object* v_fvars_3221_, lean_object* v_inst_3222_, lean_object* v_R_3223_, lean_object* v_a_3224_, lean_object* v_b_3225_, lean_object* v_c_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3219_, v_fst_3220_, v_fvars_3221_, v_inst_3222_, v_R_3223_, v_a_3224_, v_b_3225_, v_c_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec_ref(v_fst_3220_);
lean_dec(v_upperBound_3219_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3236_, lean_object* v_m_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3237_, v_a_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3240_, lean_object* v_m_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3240_, v_m_3241_, v_a_3242_);
lean_dec_ref(v_a_3242_);
lean_dec_ref(v_m_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3244_, lean_object* v_a_3245_, lean_object* v_x_3246_){
_start:
{
uint8_t v___x_3247_; 
v___x_3247_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3245_, v_x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3248_, lean_object* v_a_3249_, lean_object* v_x_3250_){
_start:
{
uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_res_3251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3248_, v_a_3249_, v_x_3250_);
lean_dec(v_x_3250_);
lean_dec_ref(v_a_3249_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3253_, lean_object* v_data_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3256_, lean_object* v_a_3257_, lean_object* v_b_3258_, lean_object* v_x_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3257_, v_b_3258_, v_x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3261_, lean_object* v_a_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3265_, lean_object* v_a_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3265_, v_a_3266_, v_x_3267_);
lean_dec(v_x_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3269_, lean_object* v_a_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3270_, v_x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3273_, lean_object* v_a_3274_, lean_object* v_x_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3273_, v_a_3274_, v_x_3275_);
lean_dec(v_x_3275_);
lean_dec_ref(v_a_3274_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3277_, lean_object* v_i_3278_, lean_object* v_source_3279_, lean_object* v_target_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3278_, v_source_3279_, v_target_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3283_, v_x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v_a_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3295_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3286_, v_a_3291_);
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref(v___x_3295_);
v___x_3297_ = lean_box(0);
v___x_3298_ = 1;
v___x_3299_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3297_, v_a_3296_, v___x_3298_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3310_, size_t v_i_3311_, lean_object* v_bs_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_usize_dec_lt(v_i_3311_, v_sz_3310_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v_bs_3312_);
return v___x_3322_;
}
else
{
lean_object* v_v_3323_; lean_object* v___x_3324_; 
v_v_3323_ = lean_array_uget_borrowed(v_bs_3312_, v_i_3311_);
lean_inc(v_v_3323_);
v___x_3324_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3323_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; lean_object* v_bs_x27_3327_; size_t v___x_3328_; size_t v___x_3329_; lean_object* v___x_3330_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = lean_unsigned_to_nat(0u);
v_bs_x27_3327_ = lean_array_uset(v_bs_3312_, v_i_3311_, v___x_3326_);
v___x_3328_ = ((size_t)1ULL);
v___x_3329_ = lean_usize_add(v_i_3311_, v___x_3328_);
v___x_3330_ = lean_array_uset(v_bs_x27_3327_, v_i_3311_, v_a_3325_);
v_i_3311_ = v___x_3329_;
v_bs_3312_ = v___x_3330_;
goto _start;
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref(v_bs_3312_);
v_a_3332_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3324_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3324_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3340_, lean_object* v_i_3341_, lean_object* v_bs_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
size_t v_sz_boxed_3351_; size_t v_i_boxed_3352_; lean_object* v_res_3353_; 
v_sz_boxed_3351_ = lean_unbox_usize(v_sz_3340_);
lean_dec(v_sz_3340_);
v_i_boxed_3352_ = lean_unbox_usize(v_i_3341_);
lean_dec(v_i_3341_);
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3351_, v_i_boxed_3352_, v_bs_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; uint8_t v_merge_3374_; 
v_merge_3374_ = lean_ctor_get_uint8(v_a_3355_, 6);
if (v_merge_3374_ == 0)
{
v___y_3364_ = v_a_3355_;
v___y_3365_ = v_a_3356_;
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
v___y_3369_ = v_a_3360_;
v___y_3370_ = v_a_3361_;
goto v___jp_3363_;
}
else
{
uint8_t v_useContext_3375_; 
v_useContext_3375_ = lean_ctor_get_uint8(v_a_3355_, 7);
if (v_useContext_3375_ == 0)
{
v___y_3364_ = v_a_3355_;
v___y_3365_ = v_a_3356_;
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
v___y_3369_ = v_a_3360_;
v___y_3370_ = v_a_3361_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_dec_ref(v___x_3376_);
v___y_3364_ = v_a_3355_;
v___y_3365_ = v_a_3356_;
v___y_3366_ = v_a_3357_;
v___y_3367_ = v_a_3358_;
v___y_3368_ = v_a_3359_;
v___y_3369_ = v_a_3360_;
v___y_3370_ = v_a_3361_;
goto v___jp_3363_;
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v_es_3354_);
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
v___jp_3363_:
{
size_t v_sz_3371_; size_t v___x_3372_; lean_object* v___x_3373_; 
v_sz_3371_ = lean_array_size(v_es_3354_);
v___x_3372_ = ((size_t)0ULL);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3371_, v___x_3372_, v_es_3354_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Meta_ExtractLets_extract(v_es_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3395_, v_x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
v_a_3411_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3402_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3402_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3419_, lean_object* v_x_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3419_, v_x_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3427_, lean_object* v_decls_3428_, lean_object* v_x_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3428_, v_x_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3436_, lean_object* v_decls_3437_, lean_object* v_x_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3436_, v_decls_3437_, v_x_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3445_, size_t v_i_3446_, lean_object* v_bs_3447_){
_start:
{
uint8_t v___x_3448_; 
v___x_3448_ = lean_usize_dec_lt(v_i_3446_, v_sz_3445_);
if (v___x_3448_ == 0)
{
return v_bs_3447_;
}
else
{
lean_object* v_v_3449_; lean_object* v___x_3450_; lean_object* v_bs_x27_3451_; lean_object* v___x_3452_; size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v_v_3449_ = lean_array_uget(v_bs_3447_, v_i_3446_);
v___x_3450_ = lean_unsigned_to_nat(0u);
v_bs_x27_3451_ = lean_array_uset(v_bs_3447_, v_i_3446_, v___x_3450_);
v___x_3452_ = l_Lean_LocalDecl_fvarId(v_v_3449_);
lean_dec(v_v_3449_);
v___x_3453_ = ((size_t)1ULL);
v___x_3454_ = lean_usize_add(v_i_3446_, v___x_3453_);
v___x_3455_ = lean_array_uset(v_bs_x27_3451_, v_i_3446_, v___x_3452_);
v_i_3446_ = v___x_3454_;
v_bs_3447_ = v___x_3455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3457_, lean_object* v_i_3458_, lean_object* v_bs_3459_){
_start:
{
size_t v_sz_boxed_3460_; size_t v_i_boxed_3461_; lean_object* v_res_3462_; 
v_sz_boxed_3460_ = lean_unbox_usize(v_sz_3457_);
lean_dec(v_sz_3457_);
v_i_boxed_3461_ = lean_unbox_usize(v_i_3458_);
lean_dec(v_i_3458_);
v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3460_, v_i_boxed_3461_, v_bs_3459_);
return v_res_3462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_unsigned_to_nat(16u);
v___x_3465_ = lean_mk_array(v___x_3464_, v___x_3463_);
return v___x_3465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
lean_ctor_set(v___x_3468_, 1, v___x_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3469_, lean_object* v_givenNames_3470_, lean_object* v_k_3471_, lean_object* v_config_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3479_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3480_, 0, v_givenNames_3470_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
lean_ctor_set(v___x_3480_, 2, v___x_3478_);
v___x_3481_ = lean_st_mk_ref(v___x_3480_);
v___x_3482_ = lean_st_mk_ref(v___x_3478_);
v___x_3483_ = l_Lean_Meta_ExtractLets_extract(v_es_3469_, v_config_3472_, v___x_3482_, v___x_3481_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v_givenNames_3487_; lean_object* v_decls_3488_; size_t v_sz_3489_; size_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; size_t v_sz_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = lean_st_ref_get(v___x_3482_);
lean_dec(v___x_3482_);
lean_dec(v___x_3485_);
v___x_3486_ = lean_st_ref_get(v___x_3481_);
lean_dec(v___x_3481_);
v_givenNames_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_givenNames_3487_);
v_decls_3488_ = lean_ctor_get(v___x_3486_, 1);
lean_inc_ref(v_decls_3488_);
lean_dec(v___x_3486_);
v_sz_3489_ = lean_array_size(v_decls_3488_);
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_3489_, v___x_3490_, v_decls_3488_);
lean_inc_ref(v___x_3491_);
v___x_3492_ = lean_array_to_list(v___x_3491_);
v_sz_3493_ = lean_array_size(v___x_3491_);
v___x_3494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3493_, v___x_3490_, v___x_3491_);
v___x_3495_ = lean_apply_3(v_k_3471_, v___x_3494_, v_a_3484_, v_givenNames_3487_);
v___x_3496_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3492_, v___x_3495_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
return v___x_3496_;
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v___x_3482_);
lean_dec(v___x_3481_);
lean_dec_ref(v_k_3471_);
v_a_3497_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3483_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3483_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3505_, lean_object* v_givenNames_3506_, lean_object* v_k_3507_, lean_object* v_config_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3505_, v_givenNames_3506_, v_k_3507_, v_config_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec_ref(v_config_3508_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3515_, lean_object* v_es_3516_, lean_object* v_givenNames_3517_, lean_object* v_k_3518_, lean_object* v_config_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3516_, v_givenNames_3517_, v_k_3518_, v_config_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3526_, lean_object* v_es_3527_, lean_object* v_givenNames_3528_, lean_object* v_k_3529_, lean_object* v_config_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3526_, v_es_3527_, v_givenNames_3528_, v_k_3529_, v_config_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec_ref(v_config_3530_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3537_, lean_object* v_runInBase_3538_, lean_object* v_b_3539_, lean_object* v_c_3540_, lean_object* v_d_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_apply_3(v_k_3537_, v_b_3539_, v_c_3540_, v_d_3541_);
lean_inc(v___y_3545_);
lean_inc_ref(v___y_3544_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
v___x_3548_ = lean_apply_7(v_runInBase_3538_, lean_box(0), v___x_3547_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, lean_box(0));
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3549_, lean_object* v_runInBase_3550_, lean_object* v_b_3551_, lean_object* v_c_3552_, lean_object* v_d_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3549_, v_runInBase_3550_, v_b_3551_, v_c_3552_, v_d_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3560_, lean_object* v_es_3561_, lean_object* v_givenNames_3562_, lean_object* v_config_3563_, lean_object* v_runInBase_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___f_3570_; lean_object* v___x_3571_; 
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3570_, 0, v_k_3560_);
lean_closure_set(v___f_3570_, 1, v_runInBase_3564_);
v___x_3571_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3561_, v_givenNames_3562_, v___f_3570_, v_config_3563_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3572_, lean_object* v_es_3573_, lean_object* v_givenNames_3574_, lean_object* v_config_3575_, lean_object* v_runInBase_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3572_, v_es_3573_, v_givenNames_3574_, v_config_3575_, v_runInBase_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec_ref(v_config_3575_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_es_3585_, lean_object* v_givenNames_3586_, lean_object* v_k_3587_, lean_object* v_config_3588_){
_start:
{
lean_object* v_toBind_3589_; lean_object* v_liftWith_3590_; lean_object* v_restoreM_3591_; lean_object* v___f_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_toBind_3589_ = lean_ctor_get(v_inst_3583_, 1);
lean_inc(v_toBind_3589_);
lean_dec_ref(v_inst_3583_);
v_liftWith_3590_ = lean_ctor_get(v_inst_3584_, 0);
lean_inc(v_liftWith_3590_);
v_restoreM_3591_ = lean_ctor_get(v_inst_3584_, 1);
lean_inc(v_restoreM_3591_);
lean_dec_ref(v_inst_3584_);
v___f_3592_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3592_, 0, v_k_3587_);
lean_closure_set(v___f_3592_, 1, v_es_3585_);
lean_closure_set(v___f_3592_, 2, v_givenNames_3586_);
lean_closure_set(v___f_3592_, 3, v_config_3588_);
v___x_3593_ = lean_apply_2(v_liftWith_3590_, lean_box(0), v___f_3592_);
v___x_3594_ = lean_apply_1(v_restoreM_3591_, lean_box(0));
v___x_3595_ = lean_apply_4(v_toBind_3589_, lean_box(0), lean_box(0), v___x_3593_, v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3596_, lean_object* v_00_u03b1_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_es_3600_, lean_object* v_givenNames_3601_, lean_object* v_k_3602_, lean_object* v_config_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_Meta_extractLets___redArg(v_inst_3598_, v_inst_3599_, v_es_3600_, v_givenNames_3601_, v_k_3602_, v_config_3603_);
return v___x_3604_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3606_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3607_ = lean_box(0);
v___x_3608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v___x_3606_);
lean_ctor_set(v___x_3608_, 2, v___x_3605_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3609_, lean_object* v_config_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v_proofs_3621_; uint8_t v_types_3622_; uint8_t v_implicits_3623_; uint8_t v_descend_3624_; uint8_t v_underBinder_3625_; uint8_t v_usedOnly_3626_; uint8_t v_merge_3627_; uint8_t v_useContext_3628_; uint8_t v_preserveBinderNames_3629_; uint8_t v_lift_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3664_; 
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3618_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3619_ = lean_st_mk_ref(v___x_3618_);
v___x_3620_ = lean_st_mk_ref(v___x_3617_);
v_proofs_3621_ = lean_ctor_get_uint8(v_config_3610_, 0);
v_types_3622_ = lean_ctor_get_uint8(v_config_3610_, 1);
v_implicits_3623_ = lean_ctor_get_uint8(v_config_3610_, 2);
v_descend_3624_ = lean_ctor_get_uint8(v_config_3610_, 3);
v_underBinder_3625_ = lean_ctor_get_uint8(v_config_3610_, 4);
v_usedOnly_3626_ = lean_ctor_get_uint8(v_config_3610_, 5);
v_merge_3627_ = lean_ctor_get_uint8(v_config_3610_, 6);
v_useContext_3628_ = lean_ctor_get_uint8(v_config_3610_, 7);
v_preserveBinderNames_3629_ = lean_ctor_get_uint8(v_config_3610_, 9);
v_lift_3630_ = lean_ctor_get_uint8(v_config_3610_, 10);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_config_3610_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3632_ = v_config_3610_;
v_isShared_3633_ = v_isSharedCheck_3664_;
goto v_resetjp_3631_;
}
else
{
lean_dec(v_config_3610_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3664_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; lean_object* v___x_3639_; 
v___x_3634_ = lean_unsigned_to_nat(1u);
v___x_3635_ = lean_mk_empty_array_with_capacity(v___x_3634_);
v___x_3636_ = lean_array_push(v___x_3635_, v_e_3609_);
v___x_3637_ = 1;
if (v_isShared_3633_ == 0)
{
v___x_3639_ = v___x_3632_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 0, v_proofs_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 1, v_types_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 2, v_implicits_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 3, v_descend_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 4, v_underBinder_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 5, v_usedOnly_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 6, v_merge_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 7, v_useContext_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 9, v_preserveBinderNames_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3663_, 10, v_lift_3630_);
v___x_3639_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3640_; 
lean_ctor_set_uint8(v___x_3639_, 8, v___x_3637_);
v___x_3640_ = l_Lean_Meta_ExtractLets_extract(v___x_3636_, v___x_3639_, v___x_3620_, v___x_3619_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
lean_dec_ref(v___x_3639_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3654_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3643_ = v___x_3640_;
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3640_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_decls_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3645_ = lean_st_ref_get(v___x_3620_);
lean_dec(v___x_3620_);
lean_dec(v___x_3645_);
v___x_3646_ = lean_st_ref_get(v___x_3619_);
lean_dec(v___x_3619_);
v_decls_3647_ = lean_ctor_get(v___x_3646_, 1);
lean_inc_ref(v_decls_3647_);
lean_dec(v___x_3646_);
v___x_3648_ = l_Lean_instInhabitedExpr;
v___x_3649_ = lean_array_get(v___x_3648_, v_a_3641_, v___x_3616_);
lean_dec(v_a_3641_);
v___x_3650_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3647_, v___x_3649_);
lean_dec_ref(v_decls_3647_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3650_);
v___x_3652_ = v___x_3643_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v___x_3620_);
lean_dec(v___x_3619_);
v_a_3655_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3640_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3640_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3665_, lean_object* v_config_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Meta_liftLets(v_e_3665_, v_config_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
return v_res_3672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3675_ = l_Lean_stringToMessageData(v___x_3674_);
return v___x_3675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3678_, lean_object* v_mvarId_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3686_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3678_, v_mvarId_3679_, v___x_3685_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3687_, lean_object* v_mvarId_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3687_, v_mvarId_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3695_, lean_object* v_tactic_3696_, lean_object* v_mvarId_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3696_, v_mvarId_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3704_, lean_object* v_tactic_3705_, lean_object* v_mvarId_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3704_, v_tactic_3705_, v_mvarId_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3713_, lean_object* v_b_3714_, lean_object* v_c_3715_, lean_object* v_d_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v___x_3722_; 
lean_inc(v___y_3720_);
lean_inc_ref(v___y_3719_);
lean_inc(v___y_3718_);
lean_inc_ref(v___y_3717_);
v___x_3722_ = lean_apply_8(v_k_3713_, v_b_3714_, v_c_3715_, v_d_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, lean_box(0));
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3723_, lean_object* v_b_3724_, lean_object* v_c_3725_, lean_object* v_d_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3723_, v_b_3724_, v_c_3725_, v_d_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3733_, lean_object* v_givenNames_3734_, lean_object* v_k_3735_, lean_object* v_config_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___f_3742_; lean_object* v___x_3743_; 
v___f_3742_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3742_, 0, v_k_3735_);
v___x_3743_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3733_, v_givenNames_3734_, v___f_3742_, v_config_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_a_3752_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3743_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3743_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3760_, lean_object* v_givenNames_3761_, lean_object* v_k_3762_, lean_object* v_config_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3760_, v_givenNames_3761_, v_k_3762_, v_config_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec_ref(v_config_3763_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3770_, lean_object* v_es_3771_, lean_object* v_givenNames_3772_, lean_object* v_k_3773_, lean_object* v_config_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3771_, v_givenNames_3772_, v_k_3773_, v_config_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3781_, lean_object* v_es_3782_, lean_object* v_givenNames_3783_, lean_object* v_k_3784_, lean_object* v_config_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3781_, v_es_3782_, v_givenNames_3783_, v_k_3784_, v_config_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec_ref(v_config_3785_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3792_, lean_object* v_x_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3792_, v_x_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3799_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3799_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3816_, lean_object* v_x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3816_, v_x_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3824_, lean_object* v_mvarId_3825_, lean_object* v_x_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3825_, v_x_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3833_, lean_object* v_mvarId_3834_, lean_object* v_x_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3833_, v_mvarId_3834_, v_x_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3842_, lean_object* v_x_3843_, lean_object* v_x_3844_, lean_object* v_x_3845_){
_start:
{
lean_object* v_ks_3846_; lean_object* v_vs_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3871_; 
v_ks_3846_ = lean_ctor_get(v_x_3842_, 0);
v_vs_3847_ = lean_ctor_get(v_x_3842_, 1);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_x_3842_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3849_ = v_x_3842_;
v_isShared_3850_ = v_isSharedCheck_3871_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_vs_3847_);
lean_inc(v_ks_3846_);
lean_dec(v_x_3842_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3871_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3851_ = lean_array_get_size(v_ks_3846_);
v___x_3852_ = lean_nat_dec_lt(v_x_3843_, v___x_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; 
lean_dec(v_x_3843_);
v___x_3853_ = lean_array_push(v_ks_3846_, v_x_3844_);
v___x_3854_ = lean_array_push(v_vs_3847_, v_x_3845_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 1, v___x_3854_);
lean_ctor_set(v___x_3849_, 0, v___x_3853_);
v___x_3856_ = v___x_3849_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
else
{
lean_object* v_k_x27_3858_; uint8_t v___x_3859_; 
v_k_x27_3858_ = lean_array_fget_borrowed(v_ks_3846_, v_x_3843_);
v___x_3859_ = l_Lean_instBEqMVarId_beq(v_x_3844_, v_k_x27_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3861_; 
if (v_isShared_3850_ == 0)
{
v___x_3861_ = v___x_3849_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_ks_3846_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_vs_3847_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = lean_unsigned_to_nat(1u);
v___x_3863_ = lean_nat_add(v_x_3843_, v___x_3862_);
lean_dec(v_x_3843_);
v_x_3842_ = v___x_3861_;
v_x_3843_ = v___x_3863_;
goto _start;
}
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3866_ = lean_array_fset(v_ks_3846_, v_x_3843_, v_x_3844_);
v___x_3867_ = lean_array_fset(v_vs_3847_, v_x_3843_, v_x_3845_);
lean_dec(v_x_3843_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 1, v___x_3867_);
lean_ctor_set(v___x_3849_, 0, v___x_3866_);
v___x_3869_ = v___x_3849_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3872_, lean_object* v_k_3873_, lean_object* v_v_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_unsigned_to_nat(0u);
v___x_3876_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3872_, v___x_3875_, v_k_3873_, v_v_3874_);
return v___x_3876_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_3877_; size_t v___x_3878_; size_t v___x_3879_; 
v___x_3877_ = ((size_t)5ULL);
v___x_3878_ = ((size_t)1ULL);
v___x_3879_ = lean_usize_shift_left(v___x_3878_, v___x_3877_);
return v___x_3879_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3880_; size_t v___x_3881_; size_t v___x_3882_; 
v___x_3880_ = ((size_t)1ULL);
v___x_3881_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3882_ = lean_usize_sub(v___x_3881_, v___x_3880_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3884_, size_t v_x_3885_, size_t v_x_3886_, lean_object* v_x_3887_, lean_object* v_x_3888_){
_start:
{
if (lean_obj_tag(v_x_3884_) == 0)
{
lean_object* v_es_3889_; size_t v___x_3890_; size_t v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; lean_object* v_j_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v_es_3889_ = lean_ctor_get(v_x_3884_, 0);
v___x_3890_ = ((size_t)5ULL);
v___x_3891_ = ((size_t)1ULL);
v___x_3892_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1);
v___x_3893_ = lean_usize_land(v_x_3885_, v___x_3892_);
v_j_3894_ = lean_usize_to_nat(v___x_3893_);
v___x_3895_ = lean_array_get_size(v_es_3889_);
v___x_3896_ = lean_nat_dec_lt(v_j_3894_, v___x_3895_);
if (v___x_3896_ == 0)
{
lean_dec(v_j_3894_);
lean_dec(v_x_3888_);
lean_dec(v_x_3887_);
return v_x_3884_;
}
else
{
lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3933_; 
lean_inc_ref(v_es_3889_);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_x_3884_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v_x_3884_, 0);
lean_dec(v_unused_3934_);
v___x_3898_ = v_x_3884_;
v_isShared_3899_ = v_isSharedCheck_3933_;
goto v_resetjp_3897_;
}
else
{
lean_dec(v_x_3884_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3933_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v_v_3900_; lean_object* v___x_3901_; lean_object* v_xs_x27_3902_; lean_object* v___y_3904_; 
v_v_3900_ = lean_array_fget(v_es_3889_, v_j_3894_);
v___x_3901_ = lean_box(0);
v_xs_x27_3902_ = lean_array_fset(v_es_3889_, v_j_3894_, v___x_3901_);
switch(lean_obj_tag(v_v_3900_))
{
case 0:
{
lean_object* v_key_3909_; lean_object* v_val_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3920_; 
v_key_3909_ = lean_ctor_get(v_v_3900_, 0);
v_val_3910_ = lean_ctor_get(v_v_3900_, 1);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_v_3900_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3912_ = v_v_3900_;
v_isShared_3913_ = v_isSharedCheck_3920_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_val_3910_);
lean_inc(v_key_3909_);
lean_dec(v_v_3900_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3920_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
uint8_t v___x_3914_; 
v___x_3914_ = l_Lean_instBEqMVarId_beq(v_x_3887_, v_key_3909_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_del_object(v___x_3912_);
v___x_3915_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3909_, v_val_3910_, v_x_3887_, v_x_3888_);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
v___y_3904_ = v___x_3916_;
goto v___jp_3903_;
}
else
{
lean_object* v___x_3918_; 
lean_dec(v_val_3910_);
lean_dec(v_key_3909_);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 1, v_x_3888_);
lean_ctor_set(v___x_3912_, 0, v_x_3887_);
v___x_3918_ = v___x_3912_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_x_3887_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_x_3888_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
v___y_3904_ = v___x_3918_;
goto v___jp_3903_;
}
}
}
}
case 1:
{
lean_object* v_node_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3931_; 
v_node_3921_ = lean_ctor_get(v_v_3900_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_v_3900_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3923_ = v_v_3900_;
v_isShared_3924_ = v_isSharedCheck_3931_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_node_3921_);
lean_dec(v_v_3900_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3931_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
size_t v___x_3925_; size_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3925_ = lean_usize_shift_right(v_x_3885_, v___x_3890_);
v___x_3926_ = lean_usize_add(v_x_3886_, v___x_3891_);
v___x_3927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3921_, v___x_3925_, v___x_3926_, v_x_3887_, v_x_3888_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3927_);
v___x_3929_ = v___x_3923_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
v___y_3904_ = v___x_3929_;
goto v___jp_3903_;
}
}
}
default: 
{
lean_object* v___x_3932_; 
v___x_3932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3932_, 0, v_x_3887_);
lean_ctor_set(v___x_3932_, 1, v_x_3888_);
v___y_3904_ = v___x_3932_;
goto v___jp_3903_;
}
}
v___jp_3903_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = lean_array_fset(v_xs_x27_3902_, v_j_3894_, v___y_3904_);
lean_dec(v_j_3894_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3905_);
v___x_3907_ = v___x_3898_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
else
{
lean_object* v_ks_3935_; lean_object* v_vs_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3956_; 
v_ks_3935_ = lean_ctor_get(v_x_3884_, 0);
v_vs_3936_ = lean_ctor_get(v_x_3884_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_x_3884_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3938_ = v_x_3884_;
v_isShared_3939_ = v_isSharedCheck_3956_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_vs_3936_);
lean_inc(v_ks_3935_);
lean_dec(v_x_3884_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3956_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_ks_3935_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_vs_3936_);
v___x_3941_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v_newNode_3942_; uint8_t v___y_3944_; size_t v___x_3950_; uint8_t v___x_3951_; 
v_newNode_3942_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3941_, v_x_3887_, v_x_3888_);
v___x_3950_ = ((size_t)7ULL);
v___x_3951_ = lean_usize_dec_le(v___x_3950_, v_x_3886_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3952_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3942_);
v___x_3953_ = lean_unsigned_to_nat(4u);
v___x_3954_ = lean_nat_dec_lt(v___x_3952_, v___x_3953_);
lean_dec(v___x_3952_);
v___y_3944_ = v___x_3954_;
goto v___jp_3943_;
}
else
{
v___y_3944_ = v___x_3951_;
goto v___jp_3943_;
}
v___jp_3943_:
{
if (v___y_3944_ == 0)
{
lean_object* v_ks_3945_; lean_object* v_vs_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v_ks_3945_ = lean_ctor_get(v_newNode_3942_, 0);
lean_inc_ref(v_ks_3945_);
v_vs_3946_ = lean_ctor_get(v_newNode_3942_, 1);
lean_inc_ref(v_vs_3946_);
lean_dec_ref(v_newNode_3942_);
v___x_3947_ = lean_unsigned_to_nat(0u);
v___x_3948_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_3949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3886_, v_ks_3945_, v_vs_3946_, v___x_3947_, v___x_3948_);
lean_dec_ref(v_vs_3946_);
lean_dec_ref(v_ks_3945_);
return v___x_3949_;
}
else
{
return v_newNode_3942_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3957_, lean_object* v_keys_3958_, lean_object* v_vals_3959_, lean_object* v_i_3960_, lean_object* v_entries_3961_){
_start:
{
lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3962_ = lean_array_get_size(v_keys_3958_);
v___x_3963_ = lean_nat_dec_lt(v_i_3960_, v___x_3962_);
if (v___x_3963_ == 0)
{
lean_dec(v_i_3960_);
return v_entries_3961_;
}
else
{
lean_object* v_k_3964_; lean_object* v_v_3965_; uint64_t v___x_3966_; size_t v_h_3967_; size_t v___x_3968_; lean_object* v___x_3969_; size_t v___x_3970_; size_t v___x_3971_; size_t v___x_3972_; size_t v_h_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v_k_3964_ = lean_array_fget_borrowed(v_keys_3958_, v_i_3960_);
v_v_3965_ = lean_array_fget_borrowed(v_vals_3959_, v_i_3960_);
v___x_3966_ = l_Lean_instHashableMVarId_hash(v_k_3964_);
v_h_3967_ = lean_uint64_to_usize(v___x_3966_);
v___x_3968_ = ((size_t)5ULL);
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = ((size_t)1ULL);
v___x_3971_ = lean_usize_sub(v_depth_3957_, v___x_3970_);
v___x_3972_ = lean_usize_mul(v___x_3968_, v___x_3971_);
v_h_3973_ = lean_usize_shift_right(v_h_3967_, v___x_3972_);
v___x_3974_ = lean_nat_add(v_i_3960_, v___x_3969_);
lean_dec(v_i_3960_);
lean_inc(v_v_3965_);
lean_inc(v_k_3964_);
v___x_3975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3961_, v_h_3973_, v_depth_3957_, v_k_3964_, v_v_3965_);
v_i_3960_ = v___x_3974_;
v_entries_3961_ = v___x_3975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3977_, lean_object* v_keys_3978_, lean_object* v_vals_3979_, lean_object* v_i_3980_, lean_object* v_entries_3981_){
_start:
{
size_t v_depth_boxed_3982_; lean_object* v_res_3983_; 
v_depth_boxed_3982_ = lean_unbox_usize(v_depth_3977_);
lean_dec(v_depth_3977_);
v_res_3983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3982_, v_keys_3978_, v_vals_3979_, v_i_3980_, v_entries_3981_);
lean_dec_ref(v_vals_3979_);
lean_dec_ref(v_keys_3978_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_, lean_object* v_x_3987_, lean_object* v_x_3988_){
_start:
{
size_t v_x_2323__boxed_3989_; size_t v_x_2324__boxed_3990_; lean_object* v_res_3991_; 
v_x_2323__boxed_3989_ = lean_unbox_usize(v_x_3985_);
lean_dec(v_x_3985_);
v_x_2324__boxed_3990_ = lean_unbox_usize(v_x_3986_);
lean_dec(v_x_3986_);
v_res_3991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3984_, v_x_2323__boxed_3989_, v_x_2324__boxed_3990_, v_x_3987_, v_x_3988_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3992_, lean_object* v_x_3993_, lean_object* v_x_3994_){
_start:
{
uint64_t v___x_3995_; size_t v___x_3996_; size_t v___x_3997_; lean_object* v___x_3998_; 
v___x_3995_ = l_Lean_instHashableMVarId_hash(v_x_3993_);
v___x_3996_ = lean_uint64_to_usize(v___x_3995_);
v___x_3997_ = ((size_t)1ULL);
v___x_3998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3992_, v___x_3996_, v___x_3997_, v_x_3993_, v_x_3994_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_3999_, lean_object* v_val_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; lean_object* v_mctx_4004_; lean_object* v_cache_4005_; lean_object* v_zetaDeltaFVarIds_4006_; lean_object* v_postponed_4007_; lean_object* v_diag_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4036_; 
v___x_4003_ = lean_st_ref_take(v___y_4001_);
v_mctx_4004_ = lean_ctor_get(v___x_4003_, 0);
v_cache_4005_ = lean_ctor_get(v___x_4003_, 1);
v_zetaDeltaFVarIds_4006_ = lean_ctor_get(v___x_4003_, 2);
v_postponed_4007_ = lean_ctor_get(v___x_4003_, 3);
v_diag_4008_ = lean_ctor_get(v___x_4003_, 4);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4010_ = v___x_4003_;
v_isShared_4011_ = v_isSharedCheck_4036_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_diag_4008_);
lean_inc(v_postponed_4007_);
lean_inc(v_zetaDeltaFVarIds_4006_);
lean_inc(v_cache_4005_);
lean_inc(v_mctx_4004_);
lean_dec(v___x_4003_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4036_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v_depth_4012_; lean_object* v_levelAssignDepth_4013_; lean_object* v_lmvarCounter_4014_; lean_object* v_mvarCounter_4015_; lean_object* v_lDecls_4016_; lean_object* v_decls_4017_; lean_object* v_userNames_4018_; lean_object* v_lAssignment_4019_; lean_object* v_eAssignment_4020_; lean_object* v_dAssignment_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4035_; 
v_depth_4012_ = lean_ctor_get(v_mctx_4004_, 0);
v_levelAssignDepth_4013_ = lean_ctor_get(v_mctx_4004_, 1);
v_lmvarCounter_4014_ = lean_ctor_get(v_mctx_4004_, 2);
v_mvarCounter_4015_ = lean_ctor_get(v_mctx_4004_, 3);
v_lDecls_4016_ = lean_ctor_get(v_mctx_4004_, 4);
v_decls_4017_ = lean_ctor_get(v_mctx_4004_, 5);
v_userNames_4018_ = lean_ctor_get(v_mctx_4004_, 6);
v_lAssignment_4019_ = lean_ctor_get(v_mctx_4004_, 7);
v_eAssignment_4020_ = lean_ctor_get(v_mctx_4004_, 8);
v_dAssignment_4021_ = lean_ctor_get(v_mctx_4004_, 9);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_mctx_4004_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4023_ = v_mctx_4004_;
v_isShared_4024_ = v_isSharedCheck_4035_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_dAssignment_4021_);
lean_inc(v_eAssignment_4020_);
lean_inc(v_lAssignment_4019_);
lean_inc(v_userNames_4018_);
lean_inc(v_decls_4017_);
lean_inc(v_lDecls_4016_);
lean_inc(v_mvarCounter_4015_);
lean_inc(v_lmvarCounter_4014_);
lean_inc(v_levelAssignDepth_4013_);
lean_inc(v_depth_4012_);
lean_dec(v_mctx_4004_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4035_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4025_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_4020_, v_mvarId_3999_, v_val_4000_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 8, v___x_4025_);
v___x_4027_ = v___x_4023_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_depth_4012_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_levelAssignDepth_4013_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v_lmvarCounter_4014_);
lean_ctor_set(v_reuseFailAlloc_4034_, 3, v_mvarCounter_4015_);
lean_ctor_set(v_reuseFailAlloc_4034_, 4, v_lDecls_4016_);
lean_ctor_set(v_reuseFailAlloc_4034_, 5, v_decls_4017_);
lean_ctor_set(v_reuseFailAlloc_4034_, 6, v_userNames_4018_);
lean_ctor_set(v_reuseFailAlloc_4034_, 7, v_lAssignment_4019_);
lean_ctor_set(v_reuseFailAlloc_4034_, 8, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4034_, 9, v_dAssignment_4021_);
v___x_4027_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4029_; 
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v___x_4027_);
v___x_4029_ = v___x_4010_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_cache_4005_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_zetaDeltaFVarIds_4006_);
lean_ctor_set(v_reuseFailAlloc_4033_, 3, v_postponed_4007_);
lean_ctor_set(v_reuseFailAlloc_4033_, 4, v_diag_4008_);
v___x_4029_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = lean_st_ref_set(v___y_4001_, v___x_4029_);
v___x_4031_ = lean_box(0);
v___x_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4037_, lean_object* v_val_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4037_, v_val_4038_, v___y_4039_);
lean_dec(v___y_4039_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4042_, size_t v_i_4043_, lean_object* v_bs_4044_){
_start:
{
uint8_t v___x_4045_; 
v___x_4045_ = lean_usize_dec_lt(v_i_4043_, v_sz_4042_);
if (v___x_4045_ == 0)
{
return v_bs_4044_;
}
else
{
lean_object* v_v_4046_; lean_object* v___x_4047_; lean_object* v_bs_x27_4048_; lean_object* v___x_4049_; size_t v___x_4050_; size_t v___x_4051_; lean_object* v___x_4052_; 
v_v_4046_ = lean_array_uget(v_bs_4044_, v_i_4043_);
v___x_4047_ = lean_unsigned_to_nat(0u);
v_bs_x27_4048_ = lean_array_uset(v_bs_4044_, v_i_4043_, v___x_4047_);
v___x_4049_ = l_Lean_Expr_fvar___override(v_v_4046_);
v___x_4050_ = ((size_t)1ULL);
v___x_4051_ = lean_usize_add(v_i_4043_, v___x_4050_);
v___x_4052_ = lean_array_uset(v_bs_x27_4048_, v_i_4043_, v___x_4049_);
v_i_4043_ = v___x_4051_;
v_bs_4044_ = v___x_4052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4054_, lean_object* v_i_4055_, lean_object* v_bs_4056_){
_start:
{
size_t v_sz_boxed_4057_; size_t v_i_boxed_4058_; lean_object* v_res_4059_; 
v_sz_boxed_4057_ = lean_unbox_usize(v_sz_4054_);
lean_dec(v_sz_4054_);
v_i_boxed_4058_ = lean_unbox_usize(v_i_4055_);
lean_dec(v_i_4055_);
v_res_4059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4057_, v_i_boxed_4058_, v_bs_4056_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4060_, lean_object* v_mvarId_4061_, lean_object* v___x_4062_, lean_object* v_a_4063_, lean_object* v_fvarIds_4064_, lean_object* v_es_4065_, lean_object* v_givenNames_x27_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; uint8_t v___y_4124_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4072_ = lean_unsigned_to_nat(0u);
v___x_4073_ = lean_array_get_borrowed(v___x_4060_, v_es_4065_, v___x_4072_);
v___x_4134_ = lean_array_get_size(v_fvarIds_4064_);
v___x_4135_ = lean_nat_dec_eq(v___x_4134_, v___x_4072_);
if (v___x_4135_ == 0)
{
v___y_4124_ = v___x_4135_;
goto v___jp_4123_;
}
else
{
uint8_t v___x_4136_; 
v___x_4136_ = lean_expr_eqv(v_a_4063_, v___x_4073_);
v___y_4124_ = v___x_4136_;
goto v___jp_4123_;
}
v___jp_4074_:
{
lean_object* v___x_4075_; 
lean_inc(v_mvarId_4061_);
v___x_4075_ = l_Lean_MVarId_getTag(v_mvarId_4061_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref(v___x_4075_);
lean_inc(v___x_4073_);
v___x_4077_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4073_, v_a_4076_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; size_t v_sz_4079_; size_t v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; uint8_t v___x_4083_; uint8_t v___x_4084_; lean_object* v___x_4085_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc_n(v_a_4078_, 2);
lean_dec_ref(v___x_4077_);
v_sz_4079_ = lean_array_size(v_fvarIds_4064_);
v___x_4080_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4064_);
v___x_4081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4079_, v___x_4080_, v_fvarIds_4064_);
v___x_4082_ = 0;
v___x_4083_ = 1;
v___x_4084_ = 1;
v___x_4085_ = l_Lean_Meta_mkLetFVars(v___x_4081_, v_a_4078_, v___x_4082_, v___x_4083_, v___x_4084_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec_ref(v___x_4081_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v_a_4086_; lean_object* v___x_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4097_; 
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref(v___x_4085_);
v___x_4087_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4061_, v_a_4086_, v___y_4068_);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; 
v_unused_4098_ = lean_ctor_get(v___x_4087_, 0);
lean_dec(v_unused_4098_);
v___x_4089_ = v___x_4087_;
v_isShared_4090_ = v_isSharedCheck_4097_;
goto v_resetjp_4088_;
}
else
{
lean_dec(v___x_4087_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4097_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4095_; 
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v_fvarIds_4064_);
lean_ctor_set(v___x_4091_, 1, v_givenNames_x27_4066_);
v___x_4092_ = l_Lean_Expr_mvarId_x21(v_a_4078_);
lean_dec(v_a_4078_);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4093_);
v___x_4095_ = v___x_4089_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_a_4078_);
lean_dec(v_givenNames_x27_4066_);
lean_dec_ref(v_fvarIds_4064_);
lean_dec(v_mvarId_4061_);
v_a_4099_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4085_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4085_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v_givenNames_x27_4066_);
lean_dec_ref(v_fvarIds_4064_);
lean_dec(v_mvarId_4061_);
v_a_4107_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4077_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4077_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec(v_givenNames_x27_4066_);
lean_dec_ref(v_fvarIds_4064_);
lean_dec(v_mvarId_4061_);
v_a_4115_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4075_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4075_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
v___jp_4123_:
{
if (v___y_4124_ == 0)
{
lean_dec(v___x_4062_);
goto v___jp_4074_;
}
else
{
lean_object* v___x_4125_; 
lean_inc(v_mvarId_4061_);
v___x_4125_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4062_, v_mvarId_4061_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_dec_ref(v___x_4125_);
goto v___jp_4074_;
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec(v_givenNames_x27_4066_);
lean_dec_ref(v_fvarIds_4064_);
lean_dec(v_mvarId_4061_);
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4137_, lean_object* v_mvarId_4138_, lean_object* v___x_4139_, lean_object* v_a_4140_, lean_object* v_fvarIds_4141_, lean_object* v_es_4142_, lean_object* v_givenNames_x27_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_MVarId_extractLets___lam__0(v___x_4137_, v_mvarId_4138_, v___x_4139_, v_a_4140_, v_fvarIds_4141_, v_es_4142_, v_givenNames_x27_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec_ref(v_es_4142_);
lean_dec_ref(v_a_4140_);
lean_dec_ref(v___x_4137_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4150_, lean_object* v___x_4151_, lean_object* v___x_4152_, lean_object* v_givenNames_4153_, lean_object* v_config_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; 
lean_inc(v___x_4151_);
lean_inc(v_mvarId_4150_);
v___x_4160_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4150_, v___x_4151_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v___x_4161_; 
lean_dec_ref(v___x_4160_);
lean_inc(v_mvarId_4150_);
v___x_4161_ = l_Lean_MVarId_getType(v_mvarId_4150_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___f_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc_n(v_a_4162_, 2);
lean_dec_ref(v___x_4161_);
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4163_, 0, v___x_4152_);
lean_closure_set(v___f_4163_, 1, v_mvarId_4150_);
lean_closure_set(v___f_4163_, 2, v___x_4151_);
lean_closure_set(v___f_4163_, 3, v_a_4162_);
v___x_4164_ = lean_unsigned_to_nat(1u);
v___x_4165_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___x_4166_ = lean_array_push(v___x_4165_, v_a_4162_);
v___x_4167_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4166_, v_givenNames_4153_, v___f_4163_, v_config_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
return v___x_4167_;
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_givenNames_4153_);
lean_dec_ref(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v_mvarId_4150_);
v_a_4168_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4161_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4161_);
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
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec(v_givenNames_4153_);
lean_dec_ref(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v_mvarId_4150_);
v_a_4176_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4160_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4160_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4184_, lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v_givenNames_4187_, lean_object* v_config_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4184_, v___x_4185_, v___x_4186_, v_givenNames_4187_, v_config_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec_ref(v_config_4188_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4198_, lean_object* v_givenNames_4199_, lean_object* v_config_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___f_4208_; lean_object* v___x_4209_; 
v___x_4206_ = l_Lean_instInhabitedExpr;
v___x_4207_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4198_);
v___f_4208_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4208_, 0, v_mvarId_4198_);
lean_closure_set(v___f_4208_, 1, v___x_4207_);
lean_closure_set(v___f_4208_, 2, v___x_4206_);
lean_closure_set(v___f_4208_, 3, v_givenNames_4199_);
lean_closure_set(v___f_4208_, 4, v_config_4200_);
v___x_4209_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4198_, v___f_4208_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4210_, lean_object* v_givenNames_4211_, lean_object* v_config_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_MVarId_extractLets(v_mvarId_4210_, v_givenNames_4211_, v_config_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4219_, lean_object* v_val_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4219_, v_val_4220_, v___y_4222_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4227_, lean_object* v_val_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4227_, v_val_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4235_, lean_object* v_x_4236_, lean_object* v_x_4237_, lean_object* v_x_4238_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4236_, v_x_4237_, v_x_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4240_, lean_object* v_x_4241_, size_t v_x_4242_, size_t v_x_4243_, lean_object* v_x_4244_, lean_object* v_x_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4241_, v_x_4242_, v_x_4243_, v_x_4244_, v_x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4247_, lean_object* v_x_4248_, lean_object* v_x_4249_, lean_object* v_x_4250_, lean_object* v_x_4251_, lean_object* v_x_4252_){
_start:
{
size_t v_x_2827__boxed_4253_; size_t v_x_2828__boxed_4254_; lean_object* v_res_4255_; 
v_x_2827__boxed_4253_ = lean_unbox_usize(v_x_4249_);
lean_dec(v_x_4249_);
v_x_2828__boxed_4254_ = lean_unbox_usize(v_x_4250_);
lean_dec(v_x_4250_);
v_res_4255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4247_, v_x_4248_, v_x_2827__boxed_4253_, v_x_2828__boxed_4254_, v_x_4251_, v_x_4252_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4256_, lean_object* v_n_4257_, lean_object* v_k_4258_, lean_object* v_v_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4257_, v_k_4258_, v_v_4259_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4261_, size_t v_depth_4262_, lean_object* v_keys_4263_, lean_object* v_vals_4264_, lean_object* v_heq_4265_, lean_object* v_i_4266_, lean_object* v_entries_4267_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4262_, v_keys_4263_, v_vals_4264_, v_i_4266_, v_entries_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4269_, lean_object* v_depth_4270_, lean_object* v_keys_4271_, lean_object* v_vals_4272_, lean_object* v_heq_4273_, lean_object* v_i_4274_, lean_object* v_entries_4275_){
_start:
{
size_t v_depth_boxed_4276_; lean_object* v_res_4277_; 
v_depth_boxed_4276_ = lean_unbox_usize(v_depth_4270_);
lean_dec(v_depth_4270_);
v_res_4277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4269_, v_depth_boxed_4276_, v_keys_4271_, v_vals_4272_, v_heq_4273_, v_i_4274_, v_entries_4275_);
lean_dec_ref(v_vals_4272_);
lean_dec_ref(v_keys_4271_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_, lean_object* v_x_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4279_, v_x_4280_, v_x_4281_, v_x_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4284_, size_t v_i_4285_, lean_object* v_bs_4286_){
_start:
{
uint8_t v___x_4287_; 
v___x_4287_ = lean_usize_dec_lt(v_i_4285_, v_sz_4284_);
if (v___x_4287_ == 0)
{
return v_bs_4286_;
}
else
{
lean_object* v_v_4288_; lean_object* v___x_4289_; lean_object* v_bs_x27_4290_; lean_object* v___x_4291_; size_t v___x_4292_; size_t v___x_4293_; lean_object* v___x_4294_; 
v_v_4288_ = lean_array_uget(v_bs_4286_, v_i_4285_);
v___x_4289_ = lean_unsigned_to_nat(0u);
v_bs_x27_4290_ = lean_array_uset(v_bs_4286_, v_i_4285_, v___x_4289_);
v___x_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4291_, 0, v_v_4288_);
v___x_4292_ = ((size_t)1ULL);
v___x_4293_ = lean_usize_add(v_i_4285_, v___x_4292_);
v___x_4294_ = lean_array_uset(v_bs_x27_4290_, v_i_4285_, v___x_4291_);
v_i_4285_ = v___x_4293_;
v_bs_4286_ = v___x_4294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4296_, lean_object* v_i_4297_, lean_object* v_bs_4298_){
_start:
{
size_t v_sz_boxed_4299_; size_t v_i_boxed_4300_; lean_object* v_res_4301_; 
v_sz_boxed_4299_ = lean_unbox_usize(v_sz_4296_);
lean_dec(v_sz_4296_);
v_i_boxed_4300_ = lean_unbox_usize(v_i_4297_);
lean_dec(v_i_4297_);
v_res_4301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4299_, v_i_boxed_4300_, v_bs_4298_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4302_, lean_object* v_fvars_4303_, lean_object* v_fvarIds_4304_, lean_object* v_givenNames_x27_4305_, lean_object* v_targetNew_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
lean_inc(v_mvarId_4302_);
v___x_4312_ = l_Lean_MVarId_getTag(v_mvarId_4302_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref(v___x_4312_);
v___x_4314_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4306_, v_a_4313_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; size_t v_sz_4316_; size_t v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; uint8_t v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc_n(v_a_4315_, 2);
lean_dec_ref(v___x_4314_);
v_sz_4316_ = lean_array_size(v_fvarIds_4304_);
v___x_4317_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4304_);
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4316_, v___x_4317_, v_fvarIds_4304_);
v___x_4319_ = 0;
v___x_4320_ = 1;
v___x_4321_ = 1;
v___x_4322_ = l_Lean_Meta_mkLetFVars(v___x_4318_, v_a_4315_, v___x_4319_, v___x_4320_, v___x_4321_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec_ref(v___x_4318_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4337_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4302_, v_a_4323_, v___y_4308_);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4337_ == 0)
{
lean_object* v_unused_4338_; 
v_unused_4338_ = lean_ctor_get(v___x_4324_, 0);
lean_dec(v_unused_4338_);
v___x_4326_ = v___x_4324_;
v_isShared_4327_ = v_isSharedCheck_4337_;
goto v_resetjp_4325_;
}
else
{
lean_dec(v___x_4324_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4337_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; size_t v_sz_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4328_, 0, v_fvarIds_4304_);
lean_ctor_set(v___x_4328_, 1, v_givenNames_x27_4305_);
v_sz_4329_ = lean_array_size(v_fvars_4303_);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4329_, v___x_4317_, v_fvars_4303_);
v___x_4331_ = l_Lean_Expr_mvarId_x21(v_a_4315_);
lean_dec(v_a_4315_);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4330_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
v___x_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4328_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4333_);
v___x_4335_ = v___x_4326_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_a_4315_);
lean_dec(v_givenNames_x27_4305_);
lean_dec_ref(v_fvarIds_4304_);
lean_dec_ref(v_fvars_4303_);
lean_dec(v_mvarId_4302_);
v_a_4339_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4322_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4322_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec(v_givenNames_x27_4305_);
lean_dec_ref(v_fvarIds_4304_);
lean_dec_ref(v_fvars_4303_);
lean_dec(v_mvarId_4302_);
v_a_4347_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4314_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4314_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec_ref(v_targetNew_4306_);
lean_dec(v_givenNames_x27_4305_);
lean_dec_ref(v_fvarIds_4304_);
lean_dec_ref(v_fvars_4303_);
lean_dec(v_mvarId_4302_);
v_a_4355_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4312_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4312_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4363_, lean_object* v_fvars_4364_, lean_object* v_fvarIds_4365_, lean_object* v_givenNames_x27_4366_, lean_object* v_targetNew_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4363_, v_fvars_4364_, v_fvarIds_4365_, v_givenNames_x27_4366_, v_targetNew_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4374_, lean_object* v_binderName_4375_, lean_object* v_body_4376_, uint8_t v_binderInfo_4377_, lean_object* v___f_4378_, lean_object* v___x_4379_, lean_object* v_mvarId_4380_, lean_object* v_binderType_4381_, lean_object* v_fvarIds_4382_, lean_object* v_es_4383_, lean_object* v_givenNames_x27_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___y_4396_; lean_object* v___x_4406_; uint8_t v___x_4407_; 
v___x_4390_ = lean_unsigned_to_nat(0u);
v___x_4391_ = lean_array_get_borrowed(v___x_4374_, v_es_4383_, v___x_4390_);
v___x_4406_ = lean_array_get_size(v_fvarIds_4382_);
v___x_4407_ = lean_nat_dec_eq(v___x_4406_, v___x_4390_);
if (v___x_4407_ == 0)
{
v___y_4396_ = v___x_4407_;
goto v___jp_4395_;
}
else
{
uint8_t v___x_4408_; 
v___x_4408_ = lean_expr_eqv(v_binderType_4381_, v___x_4391_);
v___y_4396_ = v___x_4408_;
goto v___jp_4395_;
}
v___jp_4392_:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
lean_inc(v___x_4391_);
v___x_4393_ = l_Lean_Expr_forallE___override(v_binderName_4375_, v___x_4391_, v_body_4376_, v_binderInfo_4377_);
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc(v___y_4386_);
lean_inc_ref(v___y_4385_);
v___x_4394_ = lean_apply_8(v___f_4378_, v_fvarIds_4382_, v_givenNames_x27_4384_, v___x_4393_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, lean_box(0));
return v___x_4394_;
}
v___jp_4395_:
{
if (v___y_4396_ == 0)
{
lean_dec(v_mvarId_4380_);
lean_dec(v___x_4379_);
goto v___jp_4392_;
}
else
{
lean_object* v___x_4397_; 
v___x_4397_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4379_, v_mvarId_4380_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_dec_ref(v___x_4397_);
goto v___jp_4392_;
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec(v_givenNames_x27_4384_);
lean_dec_ref(v_fvarIds_4382_);
lean_dec_ref(v___f_4378_);
lean_dec_ref(v_body_4376_);
lean_dec(v_binderName_4375_);
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4397_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4397_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4409_, lean_object* v_binderName_4410_, lean_object* v_body_4411_, lean_object* v_binderInfo_4412_, lean_object* v___f_4413_, lean_object* v___x_4414_, lean_object* v_mvarId_4415_, lean_object* v_binderType_4416_, lean_object* v_fvarIds_4417_, lean_object* v_es_4418_, lean_object* v_givenNames_x27_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
uint8_t v_binderInfo_1852__boxed_4425_; lean_object* v_res_4426_; 
v_binderInfo_1852__boxed_4425_ = lean_unbox(v_binderInfo_4412_);
v_res_4426_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4409_, v_binderName_4410_, v_body_4411_, v_binderInfo_1852__boxed_4425_, v___f_4413_, v___x_4414_, v_mvarId_4415_, v_binderType_4416_, v_fvarIds_4417_, v_es_4418_, v_givenNames_x27_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec_ref(v_es_4418_);
lean_dec_ref(v_binderType_4416_);
lean_dec_ref(v___x_4409_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4427_, lean_object* v_declName_4428_, lean_object* v_body_4429_, uint8_t v_nondep_4430_, lean_object* v___f_4431_, lean_object* v_value_4432_, lean_object* v___x_4433_, lean_object* v_mvarId_4434_, lean_object* v_type_4435_, lean_object* v_fvarIds_4436_, lean_object* v_es_4437_, lean_object* v_givenNames_x27_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; uint8_t v___y_4452_; lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4444_ = lean_unsigned_to_nat(0u);
v___x_4445_ = lean_array_get_borrowed(v___x_4427_, v_es_4437_, v___x_4444_);
v___x_4446_ = lean_unsigned_to_nat(1u);
v___x_4447_ = lean_array_get_borrowed(v___x_4427_, v_es_4437_, v___x_4446_);
v___x_4463_ = lean_array_get_size(v_fvarIds_4436_);
v___x_4464_ = lean_nat_dec_eq(v___x_4463_, v___x_4444_);
if (v___x_4464_ == 0)
{
v___y_4452_ = v___x_4464_;
goto v___jp_4451_;
}
else
{
uint8_t v___x_4465_; 
v___x_4465_ = lean_expr_eqv(v_type_4435_, v___x_4445_);
v___y_4452_ = v___x_4465_;
goto v___jp_4451_;
}
v___jp_4448_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_inc(v___x_4447_);
lean_inc(v___x_4445_);
v___x_4449_ = l_Lean_Expr_letE___override(v_declName_4428_, v___x_4445_, v___x_4447_, v_body_4429_, v_nondep_4430_);
lean_inc(v___y_4442_);
lean_inc_ref(v___y_4441_);
lean_inc(v___y_4440_);
lean_inc_ref(v___y_4439_);
v___x_4450_ = lean_apply_8(v___f_4431_, v_fvarIds_4436_, v_givenNames_x27_4438_, v___x_4449_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, lean_box(0));
return v___x_4450_;
}
v___jp_4451_:
{
if (v___y_4452_ == 0)
{
lean_dec(v_mvarId_4434_);
lean_dec(v___x_4433_);
goto v___jp_4448_;
}
else
{
uint8_t v___x_4453_; 
v___x_4453_ = lean_expr_eqv(v_value_4432_, v___x_4447_);
if (v___x_4453_ == 0)
{
lean_dec(v_mvarId_4434_);
lean_dec(v___x_4433_);
goto v___jp_4448_;
}
else
{
lean_object* v___x_4454_; 
v___x_4454_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4433_, v_mvarId_4434_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_dec_ref(v___x_4454_);
goto v___jp_4448_;
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec(v_givenNames_x27_4438_);
lean_dec_ref(v_fvarIds_4436_);
lean_dec_ref(v___f_4431_);
lean_dec_ref(v_body_4429_);
lean_dec(v_declName_4428_);
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4454_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4454_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4466_ = _args[0];
lean_object* v_declName_4467_ = _args[1];
lean_object* v_body_4468_ = _args[2];
lean_object* v_nondep_4469_ = _args[3];
lean_object* v___f_4470_ = _args[4];
lean_object* v_value_4471_ = _args[5];
lean_object* v___x_4472_ = _args[6];
lean_object* v_mvarId_4473_ = _args[7];
lean_object* v_type_4474_ = _args[8];
lean_object* v_fvarIds_4475_ = _args[9];
lean_object* v_es_4476_ = _args[10];
lean_object* v_givenNames_x27_4477_ = _args[11];
lean_object* v___y_4478_ = _args[12];
lean_object* v___y_4479_ = _args[13];
lean_object* v___y_4480_ = _args[14];
lean_object* v___y_4481_ = _args[15];
lean_object* v___y_4482_ = _args[16];
_start:
{
uint8_t v_nondep_1927__boxed_4483_; lean_object* v_res_4484_; 
v_nondep_1927__boxed_4483_ = lean_unbox(v_nondep_4469_);
v_res_4484_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4466_, v_declName_4467_, v_body_4468_, v_nondep_1927__boxed_4483_, v___f_4470_, v_value_4471_, v___x_4472_, v_mvarId_4473_, v_type_4474_, v_fvarIds_4475_, v_es_4476_, v_givenNames_x27_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec_ref(v_es_4476_);
lean_dec_ref(v_type_4474_);
lean_dec_ref(v_value_4471_);
lean_dec_ref(v___x_4466_);
return v_res_4484_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4489_ = l_Lean_MessageData_ofFormat(v___x_4488_);
return v___x_4489_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4492_, lean_object* v___x_4493_, lean_object* v___f_4494_, lean_object* v___x_4495_, lean_object* v_givenNames_4496_, lean_object* v_config_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v___x_4503_; 
lean_inc(v_mvarId_4492_);
v___x_4503_ = l_Lean_MVarId_getType(v_mvarId_4492_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
switch(lean_obj_tag(v_a_4504_))
{
case 7:
{
lean_object* v_binderName_4505_; lean_object* v_binderType_4506_; lean_object* v_body_4507_; uint8_t v_binderInfo_4508_; lean_object* v___x_4509_; lean_object* v___f_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v_binderName_4505_ = lean_ctor_get(v_a_4504_, 0);
lean_inc(v_binderName_4505_);
v_binderType_4506_ = lean_ctor_get(v_a_4504_, 1);
lean_inc_ref_n(v_binderType_4506_, 2);
v_body_4507_ = lean_ctor_get(v_a_4504_, 2);
lean_inc_ref(v_body_4507_);
v_binderInfo_4508_ = lean_ctor_get_uint8(v_a_4504_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4504_);
v___x_4509_ = lean_box(v_binderInfo_4508_);
v___f_4510_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4510_, 0, v___x_4493_);
lean_closure_set(v___f_4510_, 1, v_binderName_4505_);
lean_closure_set(v___f_4510_, 2, v_body_4507_);
lean_closure_set(v___f_4510_, 3, v___x_4509_);
lean_closure_set(v___f_4510_, 4, v___f_4494_);
lean_closure_set(v___f_4510_, 5, v___x_4495_);
lean_closure_set(v___f_4510_, 6, v_mvarId_4492_);
lean_closure_set(v___f_4510_, 7, v_binderType_4506_);
v___x_4511_ = lean_unsigned_to_nat(1u);
v___x_4512_ = lean_mk_empty_array_with_capacity(v___x_4511_);
v___x_4513_ = lean_array_push(v___x_4512_, v_binderType_4506_);
v___x_4514_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4513_, v_givenNames_4496_, v___f_4510_, v_config_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
return v___x_4514_;
}
case 8:
{
lean_object* v_declName_4515_; lean_object* v_type_4516_; lean_object* v_value_4517_; lean_object* v_body_4518_; uint8_t v_nondep_4519_; lean_object* v___x_4520_; lean_object* v___f_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v_declName_4515_ = lean_ctor_get(v_a_4504_, 0);
lean_inc(v_declName_4515_);
v_type_4516_ = lean_ctor_get(v_a_4504_, 1);
lean_inc_ref_n(v_type_4516_, 2);
v_value_4517_ = lean_ctor_get(v_a_4504_, 2);
lean_inc_ref_n(v_value_4517_, 2);
v_body_4518_ = lean_ctor_get(v_a_4504_, 3);
lean_inc_ref(v_body_4518_);
v_nondep_4519_ = lean_ctor_get_uint8(v_a_4504_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4504_);
v___x_4520_ = lean_box(v_nondep_4519_);
v___f_4521_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4521_, 0, v___x_4493_);
lean_closure_set(v___f_4521_, 1, v_declName_4515_);
lean_closure_set(v___f_4521_, 2, v_body_4518_);
lean_closure_set(v___f_4521_, 3, v___x_4520_);
lean_closure_set(v___f_4521_, 4, v___f_4494_);
lean_closure_set(v___f_4521_, 5, v_value_4517_);
lean_closure_set(v___f_4521_, 6, v___x_4495_);
lean_closure_set(v___f_4521_, 7, v_mvarId_4492_);
lean_closure_set(v___f_4521_, 8, v_type_4516_);
v___x_4522_ = lean_unsigned_to_nat(2u);
v___x_4523_ = lean_mk_empty_array_with_capacity(v___x_4522_);
v___x_4524_ = lean_array_push(v___x_4523_, v_type_4516_);
v___x_4525_ = lean_array_push(v___x_4524_, v_value_4517_);
v___x_4526_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4525_, v_givenNames_4496_, v___f_4521_, v_config_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
return v___x_4526_;
}
default: 
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
lean_dec(v_a_4504_);
lean_dec(v_givenNames_4496_);
lean_dec_ref(v___f_4494_);
lean_dec_ref(v___x_4493_);
v___x_4527_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4528_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4495_, v_mvarId_4492_, v___x_4527_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
return v___x_4528_;
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v_givenNames_4496_);
lean_dec(v___x_4495_);
lean_dec_ref(v___f_4494_);
lean_dec_ref(v___x_4493_);
lean_dec(v_mvarId_4492_);
v_a_4529_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4503_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4503_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4537_, lean_object* v___x_4538_, lean_object* v___f_4539_, lean_object* v___x_4540_, lean_object* v_givenNames_4541_, lean_object* v_config_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4537_, v___x_4538_, v___f_4539_, v___x_4540_, v_givenNames_4541_, v_config_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec_ref(v_config_4542_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4549_, lean_object* v___x_4550_, lean_object* v_givenNames_4551_, lean_object* v_config_4552_, lean_object* v_mvarId_4553_, lean_object* v_fvars_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___f_4560_; lean_object* v___f_4561_; lean_object* v___x_4562_; 
lean_inc_n(v_mvarId_4553_, 2);
v___f_4560_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4560_, 0, v_mvarId_4553_);
lean_closure_set(v___f_4560_, 1, v_fvars_4554_);
v___f_4561_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4561_, 0, v_mvarId_4553_);
lean_closure_set(v___f_4561_, 1, v___x_4549_);
lean_closure_set(v___f_4561_, 2, v___f_4560_);
lean_closure_set(v___f_4561_, 3, v___x_4550_);
lean_closure_set(v___f_4561_, 4, v_givenNames_4551_);
lean_closure_set(v___f_4561_, 5, v_config_4552_);
v___x_4562_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4553_, v___f_4561_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4563_, lean_object* v___x_4564_, lean_object* v_givenNames_4565_, lean_object* v_config_4566_, lean_object* v_mvarId_4567_, lean_object* v_fvars_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4563_, v___x_4564_, v_givenNames_4565_, v_config_4566_, v_mvarId_4567_, v_fvars_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4575_, lean_object* v_fvarId_4576_, lean_object* v_givenNames_4577_, lean_object* v_config_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4584_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4575_);
v___x_4585_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4575_, v___x_4584_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v___x_4586_; lean_object* v___f_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; uint8_t v___x_4591_; lean_object* v___x_4592_; 
lean_dec_ref(v___x_4585_);
v___x_4586_ = l_Lean_instInhabitedExpr;
v___f_4587_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4587_, 0, v___x_4586_);
lean_closure_set(v___f_4587_, 1, v___x_4584_);
lean_closure_set(v___f_4587_, 2, v_givenNames_4577_);
lean_closure_set(v___f_4587_, 3, v_config_4578_);
v___x_4588_ = lean_unsigned_to_nat(1u);
v___x_4589_ = lean_mk_empty_array_with_capacity(v___x_4588_);
v___x_4590_ = lean_array_push(v___x_4589_, v_fvarId_4576_);
v___x_4591_ = 0;
v___x_4592_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4575_, v___x_4590_, v___f_4587_, v___x_4591_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
return v___x_4592_;
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec_ref(v_config_4578_);
lean_dec(v_givenNames_4577_);
lean_dec(v_fvarId_4576_);
lean_dec(v_mvarId_4575_);
v_a_4593_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4585_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4585_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4601_, lean_object* v_fvarId_4602_, lean_object* v_givenNames_4603_, lean_object* v_config_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4601_, v_fvarId_4602_, v_givenNames_4603_, v_config_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4611_, lean_object* v___x_4612_, lean_object* v_config_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; 
lean_inc(v___x_4612_);
lean_inc(v_mvarId_4611_);
v___x_4619_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4611_, v___x_4612_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v___x_4620_; 
lean_dec_ref(v___x_4619_);
lean_inc(v_mvarId_4611_);
v___x_4620_ = l_Lean_MVarId_getType(v_mvarId_4611_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4622_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc_n(v_a_4621_, 2);
lean_dec_ref(v___x_4620_);
v___x_4622_ = l_Lean_Meta_liftLets(v_a_4621_, v_config_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; uint8_t v___x_4624_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4623_);
lean_dec_ref(v___x_4622_);
v___x_4624_ = lean_expr_eqv(v_a_4621_, v_a_4623_);
lean_dec(v_a_4621_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; 
lean_dec(v___x_4612_);
v___x_4625_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4611_, v_a_4623_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
return v___x_4625_;
}
else
{
lean_object* v___x_4626_; 
lean_inc(v_mvarId_4611_);
v___x_4626_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4612_, v_mvarId_4611_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v___x_4627_; 
lean_dec_ref(v___x_4626_);
v___x_4627_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4611_, v_a_4623_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
return v___x_4627_;
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec(v_a_4623_);
lean_dec(v_mvarId_4611_);
v_a_4628_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4626_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4626_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_a_4621_);
lean_dec(v___x_4612_);
lean_dec(v_mvarId_4611_);
v_a_4636_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4622_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4622_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec_ref(v_config_4613_);
lean_dec(v___x_4612_);
lean_dec(v_mvarId_4611_);
v_a_4644_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4620_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4620_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec_ref(v_config_4613_);
lean_dec(v___x_4612_);
lean_dec(v_mvarId_4611_);
v_a_4652_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4619_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4619_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4660_, lean_object* v___x_4661_, lean_object* v_config_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4660_, v___x_4661_, v_config_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4672_, lean_object* v_config_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_){
_start:
{
lean_object* v___x_4679_; lean_object* v___f_4680_; lean_object* v___x_4681_; 
v___x_4679_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4672_);
v___f_4680_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4680_, 0, v_mvarId_4672_);
lean_closure_set(v___f_4680_, 1, v___x_4679_);
lean_closure_set(v___f_4680_, 2, v_config_4673_);
v___x_4681_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4672_, v___f_4680_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4682_, lean_object* v_config_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_MVarId_liftLets(v_mvarId_4682_, v_config_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4690_, lean_object* v_fvars_4691_, lean_object* v_targetNew_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4690_, v_targetNew_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4712_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4712_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4712_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4703_; size_t v_sz_4704_; size_t v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4710_; 
v___x_4703_ = lean_box(0);
v_sz_4704_ = lean_array_size(v_fvars_4691_);
v___x_4705_ = ((size_t)0ULL);
v___x_4706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4704_, v___x_4705_, v_fvars_4691_);
v___x_4707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
lean_ctor_set(v___x_4707_, 1, v_a_4699_);
v___x_4708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4703_);
lean_ctor_set(v___x_4708_, 1, v___x_4707_);
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 0, v___x_4708_);
v___x_4710_ = v___x_4701_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4708_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec_ref(v_fvars_4691_);
v_a_4713_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4698_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4698_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4721_, lean_object* v_fvars_4722_, lean_object* v_targetNew_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4721_, v_fvars_4722_, v_targetNew_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4730_, lean_object* v_config_4731_, lean_object* v___f_4732_, lean_object* v___x_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v___x_4739_; 
lean_inc(v_mvarId_4730_);
v___x_4739_ = l_Lean_MVarId_getType(v_mvarId_4730_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc(v_a_4740_);
lean_dec_ref(v___x_4739_);
switch(lean_obj_tag(v_a_4740_))
{
case 7:
{
lean_object* v_binderName_4741_; lean_object* v_binderType_4742_; lean_object* v_body_4743_; uint8_t v_binderInfo_4744_; lean_object* v___x_4745_; 
v_binderName_4741_ = lean_ctor_get(v_a_4740_, 0);
lean_inc(v_binderName_4741_);
v_binderType_4742_ = lean_ctor_get(v_a_4740_, 1);
lean_inc_ref_n(v_binderType_4742_, 2);
v_body_4743_ = lean_ctor_get(v_a_4740_, 2);
lean_inc_ref(v_body_4743_);
v_binderInfo_4744_ = lean_ctor_get_uint8(v_a_4740_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4740_);
v___x_4745_ = l_Lean_Meta_liftLets(v_binderType_4742_, v_config_4731_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; uint8_t v___x_4754_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4746_);
lean_dec_ref(v___x_4745_);
v___x_4754_ = lean_expr_eqv(v_binderType_4742_, v_a_4746_);
lean_dec_ref(v_binderType_4742_);
if (v___x_4754_ == 0)
{
lean_dec(v___x_4733_);
lean_dec(v_mvarId_4730_);
v___y_4748_ = v___y_4734_;
v___y_4749_ = v___y_4735_;
v___y_4750_ = v___y_4736_;
v___y_4751_ = v___y_4737_;
goto v___jp_4747_;
}
else
{
lean_object* v___x_4755_; 
v___x_4755_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4733_, v_mvarId_4730_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_dec_ref(v___x_4755_);
v___y_4748_ = v___y_4734_;
v___y_4749_ = v___y_4735_;
v___y_4750_ = v___y_4736_;
v___y_4751_ = v___y_4737_;
goto v___jp_4747_;
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_a_4746_);
lean_dec_ref(v_body_4743_);
lean_dec(v_binderName_4741_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec_ref(v___f_4732_);
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
v___jp_4747_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = l_Lean_Expr_forallE___override(v_binderName_4741_, v_a_4746_, v_body_4743_, v_binderInfo_4744_);
v___x_4753_ = lean_apply_6(v___f_4732_, v___x_4752_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, lean_box(0));
return v___x_4753_;
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_dec_ref(v_body_4743_);
lean_dec_ref(v_binderType_4742_);
lean_dec(v_binderName_4741_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___x_4733_);
lean_dec_ref(v___f_4732_);
lean_dec(v_mvarId_4730_);
v_a_4764_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4745_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4745_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
case 8:
{
lean_object* v_declName_4772_; lean_object* v_type_4773_; lean_object* v_value_4774_; lean_object* v_body_4775_; uint8_t v_nondep_4776_; lean_object* v___x_4777_; 
v_declName_4772_ = lean_ctor_get(v_a_4740_, 0);
lean_inc(v_declName_4772_);
v_type_4773_ = lean_ctor_get(v_a_4740_, 1);
lean_inc_ref_n(v_type_4773_, 2);
v_value_4774_ = lean_ctor_get(v_a_4740_, 2);
lean_inc_ref(v_value_4774_);
v_body_4775_ = lean_ctor_get(v_a_4740_, 3);
lean_inc_ref(v_body_4775_);
v_nondep_4776_ = lean_ctor_get_uint8(v_a_4740_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4740_);
lean_inc_ref(v_config_4731_);
v___x_4777_ = l_Lean_Meta_liftLets(v_type_4773_, v_config_4731_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4779_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref(v___x_4777_);
lean_inc_ref(v_value_4774_);
v___x_4779_ = l_Lean_Meta_liftLets(v_value_4774_, v_config_4731_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4784_; lean_object* v___y_4785_; uint8_t v___y_4789_; uint8_t v___x_4799_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref(v___x_4779_);
v___x_4799_ = lean_expr_eqv(v_type_4773_, v_a_4778_);
lean_dec_ref(v_type_4773_);
if (v___x_4799_ == 0)
{
lean_dec_ref(v_value_4774_);
v___y_4789_ = v___x_4799_;
goto v___jp_4788_;
}
else
{
uint8_t v___x_4800_; 
v___x_4800_ = lean_expr_eqv(v_value_4774_, v_a_4780_);
lean_dec_ref(v_value_4774_);
v___y_4789_ = v___x_4800_;
goto v___jp_4788_;
}
v___jp_4781_:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = l_Lean_Expr_letE___override(v_declName_4772_, v_a_4778_, v_a_4780_, v_body_4775_, v_nondep_4776_);
v___x_4787_ = lean_apply_6(v___f_4732_, v___x_4786_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, lean_box(0));
return v___x_4787_;
}
v___jp_4788_:
{
if (v___y_4789_ == 0)
{
lean_dec(v___x_4733_);
lean_dec(v_mvarId_4730_);
v___y_4782_ = v___y_4734_;
v___y_4783_ = v___y_4735_;
v___y_4784_ = v___y_4736_;
v___y_4785_ = v___y_4737_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4790_; 
v___x_4790_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4733_, v_mvarId_4730_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_dec_ref(v___x_4790_);
v___y_4782_ = v___y_4734_;
v___y_4783_ = v___y_4735_;
v___y_4784_ = v___y_4736_;
v___y_4785_ = v___y_4737_;
goto v___jp_4781_;
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
lean_dec(v_a_4780_);
lean_dec(v_a_4778_);
lean_dec_ref(v_body_4775_);
lean_dec(v_declName_4772_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec_ref(v___f_4732_);
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v_a_4778_);
lean_dec_ref(v_body_4775_);
lean_dec_ref(v_value_4774_);
lean_dec_ref(v_type_4773_);
lean_dec(v_declName_4772_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___x_4733_);
lean_dec_ref(v___f_4732_);
lean_dec(v_mvarId_4730_);
v_a_4801_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4779_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4779_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_dec_ref(v_body_4775_);
lean_dec_ref(v_value_4774_);
lean_dec_ref(v_type_4773_);
lean_dec(v_declName_4772_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___x_4733_);
lean_dec_ref(v___f_4732_);
lean_dec_ref(v_config_4731_);
lean_dec(v_mvarId_4730_);
v_a_4809_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4777_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4777_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4812_ == 0)
{
v___x_4814_ = v___x_4811_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4809_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
default: 
{
lean_object* v___x_4817_; lean_object* v___x_4818_; 
lean_dec(v_a_4740_);
lean_dec_ref(v___f_4732_);
lean_dec_ref(v_config_4731_);
v___x_4817_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4818_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4733_, v_mvarId_4730_, v___x_4817_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
return v___x_4818_;
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___x_4733_);
lean_dec_ref(v___f_4732_);
lean_dec_ref(v_config_4731_);
lean_dec(v_mvarId_4730_);
v_a_4819_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4739_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4739_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4827_, lean_object* v_config_4828_, lean_object* v___f_4829_, lean_object* v___x_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4827_, v_config_4828_, v___f_4829_, v___x_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4837_, lean_object* v___x_4838_, lean_object* v_mvarId_4839_, lean_object* v_fvars_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v___f_4846_; lean_object* v___f_4847_; lean_object* v___x_4848_; 
lean_inc_n(v_mvarId_4839_, 2);
v___f_4846_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4846_, 0, v_mvarId_4839_);
lean_closure_set(v___f_4846_, 1, v_fvars_4840_);
v___f_4847_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4847_, 0, v_mvarId_4839_);
lean_closure_set(v___f_4847_, 1, v_config_4837_);
lean_closure_set(v___f_4847_, 2, v___f_4846_);
lean_closure_set(v___f_4847_, 3, v___x_4838_);
v___x_4848_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4839_, v___f_4847_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4849_, lean_object* v___x_4850_, lean_object* v_mvarId_4851_, lean_object* v_fvars_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4849_, v___x_4850_, v_mvarId_4851_, v_fvars_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4859_, lean_object* v_fvarId_4860_, lean_object* v_config_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4859_);
v___x_4868_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4859_, v___x_4867_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v___f_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; uint8_t v___x_4873_; lean_object* v___x_4874_; 
lean_dec_ref(v___x_4868_);
v___f_4869_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4869_, 0, v_config_4861_);
lean_closure_set(v___f_4869_, 1, v___x_4867_);
v___x_4870_ = lean_unsigned_to_nat(1u);
v___x_4871_ = lean_mk_empty_array_with_capacity(v___x_4870_);
v___x_4872_ = lean_array_push(v___x_4871_, v_fvarId_4860_);
v___x_4873_ = 0;
v___x_4874_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4859_, v___x_4872_, v___f_4869_, v___x_4873_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4883_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4877_ = v___x_4874_;
v_isShared_4878_ = v_isSharedCheck_4883_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4874_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4883_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v_snd_4879_; lean_object* v___x_4881_; 
v_snd_4879_ = lean_ctor_get(v_a_4875_, 1);
lean_inc(v_snd_4879_);
lean_dec(v_a_4875_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 0, v_snd_4879_);
v___x_4881_ = v___x_4877_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_snd_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
v_a_4884_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4874_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4874_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec_ref(v_config_4861_);
lean_dec(v_fvarId_4860_);
lean_dec(v_mvarId_4859_);
v_a_4892_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4868_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4868_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4900_, lean_object* v_fvarId_4901_, lean_object* v_config_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4900_, v_fvarId_4901_, v_config_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
lean_dec(v_a_4904_);
lean_dec_ref(v_a_4903_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4909_, lean_object* v___x_4910_, uint8_t v_failIfUnchanged_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v___x_4917_; 
lean_inc(v___x_4910_);
lean_inc(v_mvarId_4909_);
v___x_4917_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4909_, v___x_4910_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v___x_4918_; 
lean_dec_ref(v___x_4917_);
lean_inc(v_mvarId_4909_);
v___x_4918_ = l_Lean_MVarId_getType(v_mvarId_4909_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v_a_4919_; lean_object* v___x_4920_; 
v_a_4919_ = lean_ctor_get(v___x_4918_, 0);
lean_inc_n(v_a_4919_, 2);
lean_dec_ref(v___x_4918_);
v___x_4920_ = l_Lean_Meta_letToHave(v_a_4919_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
if (lean_obj_tag(v___x_4920_) == 0)
{
if (v_failIfUnchanged_4911_ == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; 
lean_dec(v_a_4919_);
lean_dec(v___x_4910_);
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref(v___x_4920_);
v___x_4922_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4909_, v_a_4921_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
return v___x_4922_;
}
else
{
lean_object* v_a_4923_; uint8_t v___x_4924_; 
v_a_4923_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4923_);
lean_dec_ref(v___x_4920_);
v___x_4924_ = lean_expr_eqv(v_a_4919_, v_a_4923_);
lean_dec(v_a_4919_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; 
lean_dec(v___x_4910_);
v___x_4925_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4909_, v_a_4923_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
return v___x_4925_;
}
else
{
lean_object* v___x_4926_; 
lean_inc(v_mvarId_4909_);
v___x_4926_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4910_, v_mvarId_4909_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v___x_4927_; 
lean_dec_ref(v___x_4926_);
v___x_4927_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4909_, v_a_4923_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
return v___x_4927_;
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_dec(v_a_4923_);
lean_dec(v_mvarId_4909_);
v_a_4928_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4926_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4926_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
lean_dec(v_a_4919_);
lean_dec(v___x_4910_);
lean_dec(v_mvarId_4909_);
v_a_4936_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4920_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4920_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
else
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4951_; 
lean_dec(v___x_4910_);
lean_dec(v_mvarId_4909_);
v_a_4944_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4946_ = v___x_4918_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4918_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4949_; 
if (v_isShared_4947_ == 0)
{
v___x_4949_ = v___x_4946_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4944_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec(v___x_4910_);
lean_dec(v_mvarId_4909_);
v_a_4952_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4917_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4917_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4960_, lean_object* v___x_4961_, lean_object* v_failIfUnchanged_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4968_; lean_object* v_res_4969_; 
v_failIfUnchanged_boxed_4968_ = lean_unbox(v_failIfUnchanged_4962_);
v_res_4969_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4960_, v___x_4961_, v_failIfUnchanged_boxed_4968_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4973_, uint8_t v_failIfUnchanged_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___f_4982_; lean_object* v___x_4983_; 
v___x_4980_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4981_ = lean_box(v_failIfUnchanged_4974_);
lean_inc(v_mvarId_4973_);
v___f_4982_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4982_, 0, v_mvarId_4973_);
lean_closure_set(v___f_4982_, 1, v___x_4980_);
lean_closure_set(v___f_4982_, 2, v___x_4981_);
v___x_4983_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4973_, v___f_4982_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4984_, lean_object* v_failIfUnchanged_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4991_; lean_object* v_res_4992_; 
v_failIfUnchanged_boxed_4991_ = lean_unbox(v_failIfUnchanged_4985_);
v_res_4992_ = l_Lean_MVarId_letToHave(v_mvarId_4984_, v_failIfUnchanged_boxed_4991_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v_a_4986_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4993_, lean_object* v___x_4994_, lean_object* v_fvarId_4995_, uint8_t v_failIfUnchanged_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v___x_5002_; 
lean_inc(v___x_4994_);
lean_inc(v_mvarId_4993_);
v___x_5002_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4993_, v___x_4994_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v___x_5003_; 
lean_dec_ref(v___x_5002_);
lean_inc(v_fvarId_4995_);
v___x_5003_ = l_Lean_FVarId_getType___redArg(v_fvarId_4995_, v___y_4997_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5005_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc_n(v_a_5004_, 2);
lean_dec_ref(v___x_5003_);
v___x_5005_ = l_Lean_Meta_letToHave(v_a_5004_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5005_) == 0)
{
if (v_failIfUnchanged_4996_ == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5007_; 
lean_dec(v_a_5004_);
lean_dec(v___x_4994_);
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5006_);
lean_dec_ref(v___x_5005_);
v___x_5007_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4993_, v_fvarId_4995_, v_a_5006_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
return v___x_5007_;
}
else
{
lean_object* v_a_5008_; uint8_t v___x_5009_; 
v_a_5008_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5008_);
lean_dec_ref(v___x_5005_);
v___x_5009_ = lean_expr_eqv(v_a_5004_, v_a_5008_);
lean_dec(v_a_5004_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
lean_dec(v___x_4994_);
v___x_5010_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4993_, v_fvarId_4995_, v_a_5008_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
return v___x_5010_;
}
else
{
lean_object* v___x_5011_; 
lean_inc(v_mvarId_4993_);
v___x_5011_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4994_, v_mvarId_4993_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v___x_5012_; 
lean_dec_ref(v___x_5011_);
v___x_5012_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4993_, v_fvarId_4995_, v_a_5008_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
return v___x_5012_;
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec(v_a_5008_);
lean_dec(v_fvarId_4995_);
lean_dec(v_mvarId_4993_);
v_a_5013_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_5011_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5011_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_a_5004_);
lean_dec(v_fvarId_4995_);
lean_dec(v___x_4994_);
lean_dec(v_mvarId_4993_);
v_a_5021_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_5005_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5005_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec(v_fvarId_4995_);
lean_dec(v___x_4994_);
lean_dec(v_mvarId_4993_);
v_a_5029_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5003_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5003_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
else
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5044_; 
lean_dec(v_fvarId_4995_);
lean_dec(v___x_4994_);
lean_dec(v_mvarId_4993_);
v_a_5037_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5039_ = v___x_5002_;
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5002_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5042_; 
if (v_isShared_5040_ == 0)
{
v___x_5042_ = v___x_5039_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5045_, lean_object* v___x_5046_, lean_object* v_fvarId_5047_, lean_object* v_failIfUnchanged_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5054_; lean_object* v_res_5055_; 
v_failIfUnchanged_boxed_5054_ = lean_unbox(v_failIfUnchanged_5048_);
v_res_5055_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5045_, v___x_5046_, v_fvarId_5047_, v_failIfUnchanged_boxed_5054_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5056_, lean_object* v_fvarId_5057_, uint8_t v_failIfUnchanged_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___f_5066_; lean_object* v___x_5067_; 
v___x_5064_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5065_ = lean_box(v_failIfUnchanged_5058_);
lean_inc(v_mvarId_5056_);
v___f_5066_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5066_, 0, v_mvarId_5056_);
lean_closure_set(v___f_5066_, 1, v___x_5064_);
lean_closure_set(v___f_5066_, 2, v_fvarId_5057_);
lean_closure_set(v___f_5066_, 3, v___x_5065_);
v___x_5067_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5056_, v___f_5066_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5068_, lean_object* v_fvarId_5069_, lean_object* v_failIfUnchanged_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5076_; lean_object* v_res_5077_; 
v_failIfUnchanged_boxed_5076_ = lean_unbox(v_failIfUnchanged_5070_);
v_res_5077_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5068_, v_fvarId_5069_, v_failIfUnchanged_boxed_5076_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
return v_res_5077_;
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
