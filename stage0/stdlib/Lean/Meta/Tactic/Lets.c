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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_dec_ref_known(v_givenNames_61_, 2);
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
v___x_76_ = lean_st_ref_swap(v_a_58_, v___x_75_);
lean_dec(v___x_76_);
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
lean_dec_ref_known(v_e_214_, 3);
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
lean_dec_ref_known(v_e_214_, 3);
v_d_217_ = v_binderType_223_;
v_b_218_ = v_body_224_;
goto v___jp_216_;
}
case 10:
{
lean_object* v_expr_225_; 
v_expr_225_ = lean_ctor_get(v_e_214_, 1);
lean_inc_ref(v_expr_225_);
lean_dec_ref_known(v_e_214_, 2);
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
lean_dec_ref_known(v_e_214_, 4);
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
lean_dec_ref_known(v_e_214_, 2);
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
lean_dec_ref_known(v_e_214_, 3);
v_e_214_ = v_struct_237_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_fvarId_239_ = lean_ctor_get(v_e_214_, 0);
lean_inc(v_fvarId_239_);
lean_dec_ref_known(v_e_214_, 1);
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
lean_dec_ref_known(v_a_277_, 1);
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
v___x_466_ = lean_st_ref_put(v_a_460_, v_snd_465_);
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
v___x_688_ = lean_st_ref_put(v_a_658_, v___x_687_);
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
v___x_918_ = lean_st_ref_put(v_a_904_, v___x_917_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(size_t v_sz_947_, size_t v_i_948_, lean_object* v_bs_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_950_ == 0)
{
return v_bs_949_;
}
else
{
lean_object* v_v_951_; lean_object* v_decl_952_; lean_object* v___x_953_; lean_object* v_bs_x27_954_; size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; 
v_v_951_ = lean_array_uget_borrowed(v_bs_949_, v_i_948_);
v_decl_952_ = lean_ctor_get(v_v_951_, 0);
lean_inc_ref(v_decl_952_);
v___x_953_ = lean_unsigned_to_nat(0u);
v_bs_x27_954_ = lean_array_uset(v_bs_949_, v_i_948_, v___x_953_);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_add(v_i_948_, v___x_955_);
v___x_957_ = lean_array_uset(v_bs_x27_954_, v_i_948_, v_decl_952_);
v_i_948_ = v___x_956_;
v_bs_949_ = v___x_957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1___boxed(lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_bs_961_){
_start:
{
size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_sz_boxed_962_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_963_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_boxed_962_, v_i_boxed_963_, v_bs_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; 
lean_inc(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
v___x_974_ = lean_apply_8(v_x_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, lean_box(0));
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(v_x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(lean_object* v_decls_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___f_995_; lean_object* v___x_996_; 
lean_inc(v___y_989_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
v___f_995_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_995_, 0, v_x_986_);
lean_closure_set(v___f_995_, 1, v___y_987_);
lean_closure_set(v___f_995_, 2, v___y_988_);
lean_closure_set(v___f_995_, 3, v___y_989_);
v___x_996_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_985_, v___f_995_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_996_) == 0)
{
return v___x_996_;
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___boxed(lean_object* v_decls_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(lean_object* v___x_1016_, lean_object* v_as_1017_, size_t v_i_1018_, size_t v_stop_1019_, lean_object* v_b_1020_){
_start:
{
lean_object* v___y_1022_; uint8_t v___x_1026_; 
v___x_1026_ = lean_usize_dec_eq(v_i_1018_, v_stop_1019_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v_decl_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1027_ = lean_array_uget_borrowed(v_as_1017_, v_i_1018_);
v_decl_1028_ = lean_ctor_get(v___x_1027_, 0);
v___x_1029_ = l_Lean_LocalDecl_fvarId(v_decl_1028_);
v___x_1030_ = l_Lean_LocalContext_contains(v___x_1016_, v___x_1029_);
lean_dec(v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_inc(v___x_1027_);
v___x_1031_ = lean_array_push(v_b_1020_, v___x_1027_);
v___y_1022_ = v___x_1031_;
goto v___jp_1021_;
}
else
{
v___y_1022_ = v_b_1020_;
goto v___jp_1021_;
}
}
else
{
return v_b_1020_;
}
v___jp_1021_:
{
size_t v___x_1023_; size_t v___x_1024_; 
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1018_, v___x_1023_);
v_i_1018_ = v___x_1024_;
v_b_1020_ = v___y_1022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(lean_object* v___x_1032_, lean_object* v_as_1033_, lean_object* v_i_1034_, lean_object* v_stop_1035_, lean_object* v_b_1036_){
_start:
{
size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; lean_object* v_res_1039_; 
v_i_boxed_1037_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1035_);
lean_dec(v_stop_1035_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_1032_, v_as_1033_, v_i_boxed_1037_, v_stop_boxed_1038_, v_b_1036_);
lean_dec_ref(v_as_1033_);
lean_dec_ref(v___x_1032_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(lean_object* v_decls_1040_, lean_object* v_k_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___y_1051_; lean_object* v_lctx_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_lctx_1057_ = lean_ctor_get(v___y_1045_, 2);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_array_get_size(v_decls_1040_);
v___x_1060_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_1061_ = lean_nat_dec_lt(v___x_1058_, v___x_1059_);
if (v___x_1061_ == 0)
{
v___y_1051_ = v___x_1060_;
goto v___jp_1050_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1059_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1057_, v_decls_1040_, v___x_1062_, v___x_1063_, v___x_1060_);
v___y_1051_ = v___x_1064_;
goto v___jp_1050_;
}
v___jp_1050_:
{
size_t v_sz_1052_; size_t v___x_1053_; lean_object* v_decls_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_sz_1052_ = lean_array_size(v___y_1051_);
v___x_1053_ = ((size_t)0ULL);
v_decls_1054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_1052_, v___x_1053_, v___y_1051_);
v___x_1055_ = lean_array_to_list(v_decls_1054_);
v___x_1056_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v___x_1055_, v_k_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object* v_decls_1065_, lean_object* v_k_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1065_, v_k_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v_decls_1065_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_fvarId_1076_, lean_object* v_as_1077_, lean_object* v_j_1078_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_array_get_size(v_as_1077_);
v___x_1080_ = lean_nat_dec_lt(v_j_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec(v_j_1078_);
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v_decl_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1082_ = lean_array_fget_borrowed(v_as_1077_, v_j_1078_);
v_decl_1083_ = lean_ctor_get(v___x_1082_, 0);
v___x_1084_ = l_Lean_LocalDecl_fvarId(v_decl_1083_);
v___x_1085_ = l_Lean_instBEqFVarId_beq(v___x_1084_, v_fvarId_1076_);
lean_dec(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_j_1078_, v___x_1086_);
lean_dec(v_j_1078_);
v_j_1078_ = v___x_1087_;
goto _start;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_j_1078_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_fvarId_1090_, lean_object* v_as_1091_, lean_object* v_j_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1090_, v_as_1091_, v_j_1092_);
lean_dec_ref(v_as_1091_);
lean_dec(v_fvarId_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1094_, lean_object* v_k_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v_lctx_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_st_ref_get(v_a_1098_);
v_lctx_1105_ = lean_ctor_get(v_a_1099_, 2);
v___x_1106_ = l_Lean_LocalContext_contains(v_lctx_1105_, v_fvarId_1094_);
if (v___x_1106_ == 0)
{
lean_object* v_decls_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_decls_1107_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_decls_1107_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1094_, v_decls_1107_, v___x_1108_);
if (lean_obj_tag(v___x_1109_) == 1)
{
lean_object* v_val_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_val_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_val_1110_, v___x_1111_);
lean_dec(v_val_1110_);
v___x_1113_ = l_Array_toSubarray___redArg(v_decls_1107_, v___x_1108_, v___x_1112_);
v___x_1114_ = l_Subarray_copy___redArg(v___x_1113_);
v___x_1115_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_1114_, v_k_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec_ref(v___x_1114_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
lean_dec(v___x_1109_);
lean_dec_ref(v_decls_1107_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
v___x_1116_ = lean_apply_8(v_k_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, lean_box(0));
return v___x_1116_;
}
}
else
{
lean_object* v___x_1117_; 
lean_dec(v___x_1104_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
v___x_1117_ = lean_apply_8(v_k_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, lean_box(0));
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1118_, lean_object* v_k_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1118_, v_k_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_fvarId_1118_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1129_, lean_object* v_fvarId_1130_, lean_object* v_k_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1130_, v_k_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_fvarId_1142_, lean_object* v_k_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1141_, v_fvarId_1142_, v_k_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_fvarId_1142_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object* v_00_u03b1_1153_, lean_object* v_decls_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1154_, v_x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_decls_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_1165_, v_decls_1166_, v_x_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object* v_00_u03b1_1177_, lean_object* v_decls_1178_, lean_object* v_k_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1178_, v_k_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object* v_00_u03b1_1189_, lean_object* v_decls_1190_, lean_object* v_k_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_1189_, v_decls_1190_, v_k_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_decls_1190_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_Expr_hasMVar(v_e_1201_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_e_1201_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v_mctx_1207_; lean_object* v___x_1208_; lean_object* v_fst_1209_; lean_object* v_snd_1210_; lean_object* v___x_1211_; lean_object* v_cache_1212_; lean_object* v_zetaDeltaFVarIds_1213_; lean_object* v_postponed_1214_; lean_object* v_diag_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1224_; 
v___x_1206_ = lean_st_ref_get(v___y_1202_);
v_mctx_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_ref(v_mctx_1207_);
lean_dec(v___x_1206_);
v___x_1208_ = l_Lean_instantiateMVarsCore(v_mctx_1207_, v_e_1201_);
v_fst_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_fst_1209_);
v_snd_1210_ = lean_ctor_get(v___x_1208_, 1);
lean_inc(v_snd_1210_);
lean_dec_ref(v___x_1208_);
v___x_1211_ = lean_st_ref_take(v___y_1202_);
v_cache_1212_ = lean_ctor_get(v___x_1211_, 1);
v_zetaDeltaFVarIds_1213_ = lean_ctor_get(v___x_1211_, 2);
v_postponed_1214_ = lean_ctor_get(v___x_1211_, 3);
v_diag_1215_ = lean_ctor_get(v___x_1211_, 4);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1211_, 0);
lean_dec(v_unused_1225_);
v___x_1217_ = v___x_1211_;
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_diag_1215_);
lean_inc(v_postponed_1214_);
lean_inc(v_zetaDeltaFVarIds_1213_);
lean_inc(v_cache_1212_);
lean_dec(v___x_1211_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v_snd_1210_);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_snd_1210_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_cache_1212_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_zetaDeltaFVarIds_1213_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_postponed_1214_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_diag_1215_);
v___x_1220_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_st_ref_put(v___y_1202_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_fst_1209_);
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1226_, v___y_1227_);
lean_dec(v___y_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1230_, v___y_1235_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1250_, size_t v_i_1251_, size_t v_stop_1252_, lean_object* v_b_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_a_1263_; uint8_t v___x_1269_; 
v___x_1269_ = lean_usize_dec_eq(v_i_1251_, v_stop_1252_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_array_uget_borrowed(v_as_1250_, v_i_1251_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_box(0);
v_a_1263_ = v___x_1271_;
goto v___jp_1262_;
}
else
{
lean_object* v_val_1272_; uint8_t v___y_1274_; uint8_t v___x_1301_; 
v_val_1272_ = lean_ctor_get(v___x_1270_, 0);
v___x_1301_ = l_Lean_LocalDecl_isLet(v_val_1272_, v___x_1269_);
if (v___x_1301_ == 0)
{
v___y_1274_ = v___x_1301_;
goto v___jp_1273_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1272_);
if (v___x_1302_ == 0)
{
v___y_1274_ = v___x_1301_;
goto v___jp_1273_;
}
else
{
goto v___jp_1267_;
}
}
v___jp_1273_:
{
if (v___y_1274_ == 0)
{
goto v___jp_1267_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = l_Lean_LocalDecl_value(v_val_1272_, v___x_1269_);
v___x_1276_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1275_, v___y_1258_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v_givenNames_1279_; lean_object* v_decls_1280_; lean_object* v_valueMap_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1292_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = lean_st_ref_take(v___y_1256_);
v_givenNames_1279_ = lean_ctor_get(v___x_1278_, 0);
v_decls_1280_ = lean_ctor_get(v___x_1278_, 1);
v_valueMap_1281_ = lean_ctor_get(v___x_1278_, 2);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1283_ = v___x_1278_;
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_valueMap_1281_);
lean_inc(v_decls_1280_);
lean_inc(v_givenNames_1279_);
lean_dec(v___x_1278_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1285_ = l_Lean_LocalDecl_fvarId(v_val_1272_);
v___x_1286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1281_, v_a_1277_, v___x_1285_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 2, v___x_1286_);
v___x_1288_ = v___x_1283_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_givenNames_1279_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_decls_1280_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_st_ref_put(v___y_1256_, v___x_1288_);
v___x_1290_ = lean_box(0);
v_a_1263_ = v___x_1290_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1276_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1276_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_b_1253_);
return v___x_1303_;
}
v___jp_1262_:
{
size_t v___x_1264_; size_t v___x_1265_; 
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1251_, v___x_1264_);
v_i_1251_ = v___x_1265_;
v_b_1253_ = v_a_1263_;
goto _start;
}
v___jp_1267_:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_box(0);
v_a_1263_ = v___x_1268_;
goto v___jp_1262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1304_, lean_object* v_i_1305_, lean_object* v_stop_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
size_t v_i_boxed_1316_; size_t v_stop_boxed_1317_; lean_object* v_res_1318_; 
v_i_boxed_1316_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_stop_boxed_1317_ = lean_unbox_usize(v_stop_1306_);
lean_dec(v_stop_1306_);
v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1304_, v_i_boxed_1316_, v_stop_boxed_1317_, v_b_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v_as_1304_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1319_, size_t v_i_1320_, size_t v_stop_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_a_1332_; uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_eq(v_i_1320_, v_stop_1321_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_array_uget_borrowed(v_as_1319_, v_i_1320_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_box(0);
v_a_1332_ = v___x_1340_;
goto v___jp_1331_;
}
else
{
lean_object* v_val_1341_; uint8_t v___y_1343_; uint8_t v___x_1370_; 
v_val_1341_ = lean_ctor_get(v___x_1339_, 0);
v___x_1370_ = l_Lean_LocalDecl_isLet(v_val_1341_, v___x_1338_);
if (v___x_1370_ == 0)
{
v___y_1343_ = v___x_1370_;
goto v___jp_1342_;
}
else
{
uint8_t v___x_1371_; 
v___x_1371_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1341_);
if (v___x_1371_ == 0)
{
v___y_1343_ = v___x_1370_;
goto v___jp_1342_;
}
else
{
goto v___jp_1336_;
}
}
v___jp_1342_:
{
if (v___y_1343_ == 0)
{
goto v___jp_1336_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Lean_LocalDecl_value(v_val_1341_, v___x_1338_);
v___x_1345_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1344_, v___y_1327_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; lean_object* v_givenNames_1348_; lean_object* v_decls_1349_; lean_object* v_valueMap_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1361_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = lean_st_ref_take(v___y_1325_);
v_givenNames_1348_ = lean_ctor_get(v___x_1347_, 0);
v_decls_1349_ = lean_ctor_get(v___x_1347_, 1);
v_valueMap_1350_ = lean_ctor_get(v___x_1347_, 2);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1352_ = v___x_1347_;
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_valueMap_1350_);
lean_inc(v_decls_1349_);
lean_inc(v_givenNames_1348_);
lean_dec(v___x_1347_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1354_ = l_Lean_LocalDecl_fvarId(v_val_1341_);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1350_, v_a_1346_, v___x_1354_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 2, v___x_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_givenNames_1348_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_decls_1349_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_st_ref_put(v___y_1325_, v___x_1357_);
v___x_1359_ = lean_box(0);
v_a_1332_ = v___x_1359_;
goto v___jp_1331_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1345_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1345_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_b_1322_);
return v___x_1372_;
}
v___jp_1331_:
{
size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_add(v_i_1320_, v___x_1333_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1319_, v___x_1334_, v_stop_1321_, v_a_1332_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1335_;
}
v___jp_1336_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_box(0);
v_a_1332_ = v___x_1337_;
goto v___jp_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1373_, lean_object* v_i_1374_, lean_object* v_stop_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; lean_object* v_res_1387_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1375_);
lean_dec(v_stop_1375_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1373_, v_i_boxed_1385_, v_stop_boxed_1386_, v_b_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_as_1373_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
if (lean_obj_tag(v_x_1388_) == 0)
{
lean_object* v_cs_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1411_; 
v_cs_1397_ = lean_ctor_get(v_x_1388_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_x_1388_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1399_ = v_x_1388_;
v_isShared_1400_ = v_isSharedCheck_1411_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_cs_1397_);
lean_dec(v_x_1388_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1411_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_array_get_size(v_cs_1397_);
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_nat_dec_lt(v___x_1401_, v___x_1402_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_cs_1397_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1403_);
v___x_1406_ = v___x_1399_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1403_);
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
lean_del_object(v___x_1399_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1402_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1397_, v___x_1408_, v___x_1409_, v___x_1403_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec_ref(v_cs_1397_);
return v___x_1410_;
}
}
}
else
{
lean_object* v_vs_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1426_; 
v_vs_1412_ = lean_ctor_get(v_x_1388_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1388_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1414_ = v_x_1388_;
v_isShared_1415_ = v_isSharedCheck_1426_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_vs_1412_);
lean_dec(v_x_1388_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1426_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v_vs_1412_);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_vs_1412_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1418_);
v___x_1421_ = v___x_1414_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1418_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
lean_del_object(v___x_1414_);
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1417_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1412_, v___x_1423_, v___x_1424_, v___x_1418_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec_ref(v_vs_1412_);
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1427_, size_t v_i_1428_, size_t v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_usize_dec_eq(v_i_1428_, v_stop_1429_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_array_uget_borrowed(v_as_1427_, v_i_1428_);
lean_inc(v___x_1440_);
v___x_1441_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1440_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; size_t v___x_1443_; size_t v___x_1444_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = lean_usize_add(v_i_1428_, v___x_1443_);
v_i_1428_ = v___x_1444_;
v_b_1430_ = v_a_1442_;
goto _start;
}
else
{
return v___x_1441_;
}
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1430_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1447_, lean_object* v_i_1448_, lean_object* v_stop_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
size_t v_i_boxed_1459_; size_t v_stop_boxed_1460_; lean_object* v_res_1461_; 
v_i_boxed_1459_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_stop_boxed_1460_ = lean_unbox_usize(v_stop_1449_);
lean_dec(v_stop_1449_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1447_, v_i_boxed_1459_, v_stop_boxed_1460_, v_b_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec_ref(v_as_1447_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_root_1481_; lean_object* v_tail_1482_; lean_object* v___x_1483_; 
v_root_1481_ = lean_ctor_get(v_t_1472_, 0);
lean_inc_ref(v_root_1481_);
v_tail_1482_ = lean_ctor_get(v_t_1472_, 1);
lean_inc_ref(v_tail_1482_);
lean_dec_ref(v_t_1472_);
v___x_1483_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1481_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1497_; 
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v___x_1483_, 0);
lean_dec(v_unused_1498_);
v___x_1485_ = v___x_1483_;
v_isShared_1486_ = v_isSharedCheck_1497_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v___x_1483_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1497_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = lean_array_get_size(v_tail_1482_);
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_nat_dec_lt(v___x_1487_, v___x_1488_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1492_; 
lean_dec_ref(v_tail_1482_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1489_);
v___x_1492_ = v___x_1485_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1489_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
size_t v___x_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
lean_del_object(v___x_1485_);
v___x_1494_ = ((size_t)0ULL);
v___x_1495_ = lean_usize_of_nat(v___x_1488_);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1482_, v___x_1494_, v___x_1495_, v___x_1489_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec_ref(v_tail_1482_);
return v___x_1496_;
}
}
}
else
{
lean_dec_ref(v_tail_1482_);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1508_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1510_, size_t v_x_1511_, size_t v_x_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
if (lean_obj_tag(v_x_1510_) == 0)
{
lean_object* v_cs_1521_; lean_object* v___x_1522_; size_t v___x_1523_; lean_object* v_j_1524_; lean_object* v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v_cs_1521_ = lean_ctor_get(v_x_1510_, 0);
lean_inc_ref(v_cs_1521_);
lean_dec_ref_known(v_x_1510_, 1);
v___x_1522_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1523_ = lean_usize_shift_right(v_x_1511_, v_x_1512_);
v_j_1524_ = lean_usize_to_nat(v___x_1523_);
v___x_1525_ = lean_array_get_borrowed(v___x_1522_, v_cs_1521_, v_j_1524_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_shift_left(v___x_1526_, v_x_1512_);
v___x_1528_ = lean_usize_sub(v___x_1527_, v___x_1526_);
v___x_1529_ = lean_usize_land(v_x_1511_, v___x_1528_);
v___x_1530_ = ((size_t)5ULL);
v___x_1531_ = lean_usize_sub(v_x_1512_, v___x_1530_);
lean_inc(v___x_1525_);
v___x_1532_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1525_, v___x_1529_, v___x_1531_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1547_; 
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1532_, 0);
lean_dec(v_unused_1548_);
v___x_1534_ = v___x_1532_;
v_isShared_1535_ = v_isSharedCheck_1547_;
goto v_resetjp_1533_;
}
else
{
lean_dec(v___x_1532_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1547_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_add(v_j_1524_, v___x_1536_);
lean_dec(v_j_1524_);
v___x_1538_ = lean_array_get_size(v_cs_1521_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_nat_dec_lt(v___x_1537_, v___x_1538_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1542_; 
lean_dec(v___x_1537_);
lean_dec_ref(v_cs_1521_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1539_);
v___x_1542_ = v___x_1534_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1539_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
else
{
size_t v___x_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
lean_del_object(v___x_1534_);
v___x_1544_ = lean_usize_of_nat(v___x_1537_);
lean_dec(v___x_1537_);
v___x_1545_ = lean_usize_of_nat(v___x_1538_);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1521_, v___x_1544_, v___x_1545_, v___x_1539_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec_ref(v_cs_1521_);
return v___x_1546_;
}
}
}
else
{
lean_dec(v_j_1524_);
lean_dec_ref(v_cs_1521_);
return v___x_1532_;
}
}
else
{
lean_object* v_vs_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1563_; 
v_vs_1549_ = lean_ctor_get(v_x_1510_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_x_1510_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1551_ = v_x_1510_;
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_vs_1549_);
lean_dec(v_x_1510_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1553_ = lean_usize_to_nat(v_x_1511_);
v___x_1554_ = lean_array_get_size(v_vs_1549_);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_nat_dec_lt(v___x_1553_, v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1558_; 
lean_dec(v___x_1553_);
lean_dec_ref(v_vs_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1558_ = v___x_1551_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1555_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
lean_del_object(v___x_1551_);
v___x_1560_ = lean_usize_of_nat(v___x_1553_);
lean_dec(v___x_1553_);
v___x_1561_ = lean_usize_of_nat(v___x_1554_);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1549_, v___x_1560_, v___x_1561_, v___x_1555_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec_ref(v_vs_1549_);
return v___x_1562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
size_t v_x_9183__boxed_1575_; size_t v_x_9184__boxed_1576_; lean_object* v_res_1577_; 
v_x_9183__boxed_1575_ = lean_unbox_usize(v_x_1565_);
lean_dec(v_x_1565_);
v_x_9184__boxed_1576_ = lean_unbox_usize(v_x_1566_);
lean_dec(v_x_1566_);
v_res_1577_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1564_, v_x_9183__boxed_1575_, v_x_9184__boxed_1576_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1578_, lean_object* v_start_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = lean_unsigned_to_nat(0u);
v___x_1589_ = lean_nat_dec_eq(v_start_1579_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v_root_1590_; lean_object* v_tail_1591_; size_t v_shift_1592_; lean_object* v_tailOff_1593_; uint8_t v___x_1594_; 
v_root_1590_ = lean_ctor_get(v_t_1578_, 0);
lean_inc_ref(v_root_1590_);
v_tail_1591_ = lean_ctor_get(v_t_1578_, 1);
lean_inc_ref(v_tail_1591_);
v_shift_1592_ = lean_ctor_get_usize(v_t_1578_, 4);
v_tailOff_1593_ = lean_ctor_get(v_t_1578_, 3);
lean_inc(v_tailOff_1593_);
lean_dec_ref(v_t_1578_);
v___x_1594_ = lean_nat_dec_le(v_tailOff_1593_, v_start_1579_);
if (v___x_1594_ == 0)
{
size_t v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_tailOff_1593_);
v___x_1595_ = lean_usize_of_nat(v_start_1579_);
v___x_1596_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1590_, v___x_1595_, v_shift_1592_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1609_; 
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1610_);
v___x_1598_ = v___x_1596_;
v_isShared_1599_ = v_isSharedCheck_1609_;
goto v_resetjp_1597_;
}
else
{
lean_dec(v___x_1596_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1609_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = lean_array_get_size(v_tail_1591_);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_nat_dec_lt(v___x_1588_, v___x_1600_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1604_; 
lean_dec_ref(v_tail_1591_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1601_);
v___x_1604_ = v___x_1598_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1601_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
else
{
size_t v___x_1606_; size_t v___x_1607_; lean_object* v___x_1608_; 
lean_del_object(v___x_1598_);
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = lean_usize_of_nat(v___x_1600_);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1591_, v___x_1606_, v___x_1607_, v___x_1601_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec_ref(v_tail_1591_);
return v___x_1608_;
}
}
}
else
{
lean_dec_ref(v_tail_1591_);
return v___x_1596_;
}
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
lean_dec_ref(v_root_1590_);
v___x_1611_ = lean_nat_sub(v_start_1579_, v_tailOff_1593_);
lean_dec(v_tailOff_1593_);
v___x_1612_ = lean_array_get_size(v_tail_1591_);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_nat_dec_lt(v___x_1611_, v___x_1612_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_dec(v___x_1611_);
lean_dec_ref(v_tail_1591_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
return v___x_1615_;
}
else
{
size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_usize_of_nat(v___x_1611_);
lean_dec(v___x_1611_);
v___x_1617_ = lean_usize_of_nat(v___x_1612_);
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1591_, v___x_1616_, v___x_1617_, v___x_1613_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec_ref(v_tail_1591_);
return v___x_1618_;
}
}
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1578_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1620_, lean_object* v_start_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1620_, v_start_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v_start_1621_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1631_, lean_object* v_start_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_decls_1641_; lean_object* v___x_1642_; 
v_decls_1641_ = lean_ctor_get(v_lctx_1631_, 1);
lean_inc_ref(v_decls_1641_);
lean_dec_ref(v_lctx_1631_);
v___x_1642_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1641_, v_start_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1643_, lean_object* v_start_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1643_, v_start_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v_start_1644_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_lctx_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_lctx_1662_ = lean_ctor_get(v_a_1657_, 2);
v___x_1663_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1662_);
v___x_1664_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1662_, v___x_1663_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1675_){
_start:
{
lean_object* v___f_1676_; lean_object* v___x_1677_; 
v___f_1676_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1677_ = lean_find_expr(v___f_1676_, v_e_1675_);
if (lean_obj_tag(v___x_1677_) == 0)
{
uint8_t v___x_1678_; 
v___x_1678_ = 0;
return v___x_1678_;
}
else
{
uint8_t v___x_1679_; 
lean_dec_ref_known(v___x_1677_, 1);
v___x_1679_ = 1;
return v___x_1679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1680_){
_start:
{
uint8_t v_res_1681_; lean_object* v_r_1682_; 
v_res_1681_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1680_);
lean_dec_ref(v_e_1680_);
v_r_1682_ = lean_box(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v_b_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1693_ = lean_apply_9(v_k_1683_, v_b_1687_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, lean_box(0));
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v_b_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v_b_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1705_, uint8_t v_bi_1706_, lean_object* v_type_1707_, lean_object* v_k_1708_, uint8_t v_kind_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___f_1718_; lean_object* v___x_1719_; 
lean_inc(v___y_1712_);
lean_inc(v___y_1711_);
lean_inc_ref(v___y_1710_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1718_, 0, v_k_1708_);
lean_closure_set(v___f_1718_, 1, v___y_1710_);
lean_closure_set(v___f_1718_, 2, v___y_1711_);
lean_closure_set(v___f_1718_, 3, v___y_1712_);
v___x_1719_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1705_, v_bi_1706_, v_type_1707_, v___f_1718_, v_kind_1709_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1719_) == 0)
{
return v___x_1719_;
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1728_, lean_object* v_bi_1729_, lean_object* v_type_1730_, lean_object* v_k_1731_, lean_object* v_kind_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v_bi_boxed_1741_; uint8_t v_kind_boxed_1742_; lean_object* v_res_1743_; 
v_bi_boxed_1741_ = lean_unbox(v_bi_1729_);
v_kind_boxed_1742_ = lean_unbox(v_kind_1732_);
v_res_1743_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1728_, v_bi_boxed_1741_, v_type_1730_, v_k_1731_, v_kind_boxed_1742_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1744_, lean_object* v_name_1745_, uint8_t v_bi_1746_, lean_object* v_type_1747_, lean_object* v_k_1748_, uint8_t v_kind_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1745_, v_bi_1746_, v_type_1747_, v_k_1748_, v_kind_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1759_, lean_object* v_name_1760_, lean_object* v_bi_1761_, lean_object* v_type_1762_, lean_object* v_k_1763_, lean_object* v_kind_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v_bi_boxed_1773_; uint8_t v_kind_boxed_1774_; lean_object* v_res_1775_; 
v_bi_boxed_1773_ = lean_unbox(v_bi_1761_);
v_kind_boxed_1774_ = lean_unbox(v_kind_1764_);
v_res_1775_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1759_, v_name_1760_, v_bi_boxed_1773_, v_type_1762_, v_k_1763_, v_kind_boxed_1774_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1776_, lean_object* v_e_1777_, lean_object* v___f_1778_, lean_object* v_____r_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
if (v_types_1776_ == 0)
{
lean_object* v___x_1788_; 
lean_inc_ref(v_e_1777_);
v___x_1788_ = l_Lean_Meta_isType(v_e_1777_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1799_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_unbox(v_a_1789_);
lean_dec(v_a_1789_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1791_);
lean_dec_ref(v_e_1777_);
v___x_1794_ = lean_box(0);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
v___x_1795_ = lean_apply_9(v___f_1778_, v___x_1794_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, lean_box(0));
return v___x_1795_;
}
else
{
lean_object* v___x_1797_; 
lean_dec_ref(v___f_1778_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_e_1777_);
v___x_1797_ = v___x_1791_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_e_1777_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v___f_1778_);
lean_dec_ref(v_e_1777_);
v_a_1800_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1788_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1788_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec_ref(v_e_1777_);
v___x_1808_ = lean_box(0);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
v___x_1809_ = lean_apply_9(v___f_1778_, v___x_1808_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, lean_box(0));
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1810_, lean_object* v_e_1811_, lean_object* v___f_1812_, lean_object* v_____r_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v_types_boxed_1822_; lean_object* v_res_1823_; 
v_types_boxed_1822_ = lean_unbox(v_types_1810_);
v_res_1823_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1822_, v_e_1811_, v___f_1812_, v_____r_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
return v_res_1823_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1824_, uint8_t v___y_1825_){
_start:
{
if (v___y_1825_ == 0)
{
if (v___y_1824_ == 0)
{
uint8_t v___x_1826_; 
v___x_1826_ = 1;
return v___x_1826_;
}
else
{
return v___y_1825_;
}
}
else
{
return v___y_1824_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
uint8_t v___y_41145__boxed_1829_; uint8_t v___y_41146__boxed_1830_; uint8_t v_res_1831_; lean_object* v_r_1832_; 
v___y_41145__boxed_1829_ = lean_unbox(v___y_1827_);
v___y_41146__boxed_1830_ = lean_unbox(v___y_1828_);
v_res_1831_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_41145__boxed_1829_, v___y_41146__boxed_1830_);
v_r_1832_ = lean_box(v_res_1831_);
return v_r_1832_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_instMonadEIO(lean_box(0));
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v_toApplicative_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1924_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1852_ = l_StateRefT_x27_instMonad___redArg(v___x_1851_);
v_toApplicative_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___x_1852_, 1);
lean_dec(v_unused_1925_);
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1924_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_toApplicative_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1924_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_toFunctor_1857_; lean_object* v_toSeq_1858_; lean_object* v_toSeqLeft_1859_; lean_object* v_toSeqRight_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1922_; 
v_toFunctor_1857_ = lean_ctor_get(v_toApplicative_1853_, 0);
v_toSeq_1858_ = lean_ctor_get(v_toApplicative_1853_, 2);
v_toSeqLeft_1859_ = lean_ctor_get(v_toApplicative_1853_, 3);
v_toSeqRight_1860_ = lean_ctor_get(v_toApplicative_1853_, 4);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_toApplicative_1853_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_toApplicative_1853_, 1);
lean_dec(v_unused_1923_);
v___x_1862_ = v_toApplicative_1853_;
v_isShared_1863_ = v_isSharedCheck_1922_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_toSeqRight_1860_);
lean_inc(v_toSeqLeft_1859_);
lean_inc(v_toSeq_1858_);
lean_inc(v_toFunctor_1857_);
lean_dec(v_toApplicative_1853_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1922_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___f_1864_; lean_object* v___f_1865_; lean_object* v___f_1866_; lean_object* v___f_1867_; lean_object* v___x_1868_; lean_object* v___f_1869_; lean_object* v___f_1870_; lean_object* v___f_1871_; lean_object* v___x_1873_; 
v___f_1864_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1865_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1857_);
v___f_1866_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1866_, 0, v_toFunctor_1857_);
v___f_1867_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1867_, 0, v_toFunctor_1857_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___f_1866_);
lean_ctor_set(v___x_1868_, 1, v___f_1867_);
v___f_1869_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1869_, 0, v_toSeqRight_1860_);
v___f_1870_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1870_, 0, v_toSeqLeft_1859_);
v___f_1871_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1871_, 0, v_toSeq_1858_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 4, v___f_1869_);
lean_ctor_set(v___x_1862_, 3, v___f_1870_);
lean_ctor_set(v___x_1862_, 2, v___f_1871_);
lean_ctor_set(v___x_1862_, 1, v___f_1864_);
lean_ctor_set(v___x_1862_, 0, v___x_1868_);
v___x_1873_ = v___x_1862_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___f_1864_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v___f_1871_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v___f_1870_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v___f_1869_);
v___x_1873_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___f_1865_);
lean_ctor_set(v___x_1855_, 0, v___x_1873_);
v___x_1875_ = v___x_1855_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___f_1865_);
v___x_1875_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v_toApplicative_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1918_; 
v___x_1876_ = l_StateRefT_x27_instMonad___redArg(v___x_1875_);
v_toApplicative_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1876_, 1);
lean_dec(v_unused_1919_);
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1918_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_toApplicative_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1918_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_toFunctor_1881_; lean_object* v_toSeq_1882_; lean_object* v_toSeqLeft_1883_; lean_object* v_toSeqRight_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1916_; 
v_toFunctor_1881_ = lean_ctor_get(v_toApplicative_1877_, 0);
v_toSeq_1882_ = lean_ctor_get(v_toApplicative_1877_, 2);
v_toSeqLeft_1883_ = lean_ctor_get(v_toApplicative_1877_, 3);
v_toSeqRight_1884_ = lean_ctor_get(v_toApplicative_1877_, 4);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_toApplicative_1877_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v_toApplicative_1877_, 1);
lean_dec(v_unused_1917_);
v___x_1886_ = v_toApplicative_1877_;
v_isShared_1887_ = v_isSharedCheck_1916_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_toSeqRight_1884_);
lean_inc(v_toSeqLeft_1883_);
lean_inc(v_toSeq_1882_);
lean_inc(v_toFunctor_1881_);
lean_dec(v_toApplicative_1877_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1916_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___f_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___f_1894_; lean_object* v___f_1895_; lean_object* v___f_1896_; lean_object* v___f_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___f_1900_; lean_object* v___f_1901_; lean_object* v___f_1902_; lean_object* v___x_1904_; 
v___f_1888_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1889_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1889_, 0, v___f_1888_);
v___x_1890_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1891_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1891_, 0, v___f_1889_);
lean_closure_set(v___f_1891_, 1, v___x_1890_);
v___f_1892_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1893_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1894_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1894_, 0, v___f_1892_);
lean_closure_set(v___f_1894_, 1, v___x_1893_);
v___f_1895_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1896_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1881_);
v___f_1897_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1897_, 0, v_toFunctor_1881_);
v___f_1898_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1898_, 0, v_toFunctor_1881_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___f_1897_);
lean_ctor_set(v___x_1899_, 1, v___f_1898_);
v___f_1900_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1900_, 0, v_toSeqRight_1884_);
v___f_1901_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1901_, 0, v_toSeqLeft_1883_);
v___f_1902_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1902_, 0, v_toSeq_1882_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 4, v___f_1900_);
lean_ctor_set(v___x_1886_, 3, v___f_1901_);
lean_ctor_set(v___x_1886_, 2, v___f_1902_);
lean_ctor_set(v___x_1886_, 1, v___f_1895_);
lean_ctor_set(v___x_1886_, 0, v___x_1899_);
v___x_1904_ = v___x_1886_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___f_1895_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v___f_1902_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v___f_1901_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v___f_1900_);
v___x_1904_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1906_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___f_1896_);
lean_ctor_set(v___x_1879_, 0, v___x_1904_);
v___x_1906_ = v___x_1879_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___f_1896_);
v___x_1906_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; lean_object* v___x_37996__overap_1912_; lean_object* v___x_1913_; 
v___x_1907_ = l_StateRefT_x27_instMonad___redArg(v___x_1906_);
v___x_1908_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1850_, v___f_1891_, v___f_1894_, v___x_1907_);
v___x_1909_ = l_Lean_instInhabitedExpr;
v___x_1910_ = l_instInhabitedOfMonad___redArg(v___x_1908_, v___x_1909_);
v___f_1911_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1911_, 0, v___x_1910_);
v___x_37996__overap_1912_ = lean_panic_fn_borrowed(v___f_1911_, v_msg_1841_);
lean_dec_ref(v___f_1911_);
lean_inc(v___y_1848_);
lean_inc_ref(v___y_1847_);
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc(v___y_1843_);
lean_inc_ref(v___y_1842_);
v___x_1913_ = lean_apply_8(v___x_37996__overap_1912_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, lean_box(0));
return v___x_1913_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderType_1936_, lean_object* v_binderName_1937_, uint8_t v_binderInfo_1938_, lean_object* v_body_1939_, lean_object* v_e_1940_, lean_object* v_t_1941_, lean_object* v_b_1942_){
_start:
{
size_t v___x_1943_; size_t v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = lean_ptr_addr(v_binderType_1936_);
v___x_1944_ = lean_ptr_addr(v_t_1941_);
v___x_1945_ = lean_usize_dec_eq(v___x_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Expr_lam___override(v_binderName_1937_, v_t_1941_, v_b_1942_, v_binderInfo_1938_);
return v___x_1946_;
}
else
{
size_t v___x_1947_; size_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = lean_ptr_addr(v_body_1939_);
v___x_1948_ = lean_ptr_addr(v_b_1942_);
v___x_1949_ = lean_usize_dec_eq(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Expr_lam___override(v_binderName_1937_, v_t_1941_, v_b_1942_, v_binderInfo_1938_);
return v___x_1950_;
}
else
{
uint8_t v___x_1951_; 
v___x_1951_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1938_, v_binderInfo_1938_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_Expr_lam___override(v_binderName_1937_, v_t_1941_, v_b_1942_, v_binderInfo_1938_);
return v___x_1952_;
}
else
{
lean_dec_ref(v_b_1942_);
lean_dec_ref(v_t_1941_);
lean_dec(v_binderName_1937_);
lean_inc_ref(v_e_1940_);
return v_e_1940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderType_1953_, lean_object* v_binderName_1954_, lean_object* v_binderInfo_1955_, lean_object* v_body_1956_, lean_object* v_e_1957_, lean_object* v_t_1958_, lean_object* v_b_1959_){
_start:
{
uint8_t v_binderInfo_41333__boxed_1960_; lean_object* v_res_1961_; 
v_binderInfo_41333__boxed_1960_ = lean_unbox(v_binderInfo_1955_);
v_res_1961_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderType_1953_, v_binderName_1954_, v_binderInfo_41333__boxed_1960_, v_body_1956_, v_e_1957_, v_t_1958_, v_b_1959_);
lean_dec_ref(v_e_1957_);
lean_dec_ref(v_body_1956_);
lean_dec_ref(v_binderType_1953_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderType_1962_, lean_object* v_binderName_1963_, uint8_t v_binderInfo_1964_, lean_object* v_body_1965_, lean_object* v_e_1966_, lean_object* v_t_1967_, lean_object* v_b_1968_){
_start:
{
size_t v___x_1969_; size_t v___x_1970_; uint8_t v___x_1971_; 
v___x_1969_ = lean_ptr_addr(v_binderType_1962_);
v___x_1970_ = lean_ptr_addr(v_t_1967_);
v___x_1971_ = lean_usize_dec_eq(v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_Expr_forallE___override(v_binderName_1963_, v_t_1967_, v_b_1968_, v_binderInfo_1964_);
return v___x_1972_;
}
else
{
size_t v___x_1973_; size_t v___x_1974_; uint8_t v___x_1975_; 
v___x_1973_ = lean_ptr_addr(v_body_1965_);
v___x_1974_ = lean_ptr_addr(v_b_1968_);
v___x_1975_ = lean_usize_dec_eq(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Expr_forallE___override(v_binderName_1963_, v_t_1967_, v_b_1968_, v_binderInfo_1964_);
return v___x_1976_;
}
else
{
uint8_t v___x_1977_; 
v___x_1977_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1964_, v_binderInfo_1964_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Expr_forallE___override(v_binderName_1963_, v_t_1967_, v_b_1968_, v_binderInfo_1964_);
return v___x_1978_;
}
else
{
lean_dec_ref(v_b_1968_);
lean_dec_ref(v_t_1967_);
lean_dec(v_binderName_1963_);
lean_inc_ref(v_e_1966_);
return v_e_1966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderType_1979_, lean_object* v_binderName_1980_, lean_object* v_binderInfo_1981_, lean_object* v_body_1982_, lean_object* v_e_1983_, lean_object* v_t_1984_, lean_object* v_b_1985_){
_start:
{
uint8_t v_binderInfo_41365__boxed_1986_; lean_object* v_res_1987_; 
v_binderInfo_41365__boxed_1986_ = lean_unbox(v_binderInfo_1981_);
v_res_1987_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderType_1979_, v_binderName_1980_, v_binderInfo_41365__boxed_1986_, v_body_1982_, v_e_1983_, v_t_1984_, v_b_1985_);
lean_dec_ref(v_e_1983_);
lean_dec_ref(v_body_1982_);
lean_dec_ref(v_binderType_1979_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_1988_, lean_object* v_type_1989_, lean_object* v_val_1990_, lean_object* v_k_1991_, uint8_t v_nondep_1992_, uint8_t v_kind_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___f_2002_; lean_object* v___x_2003_; 
lean_inc(v___y_1996_);
lean_inc(v___y_1995_);
lean_inc_ref(v___y_1994_);
v___f_2002_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2002_, 0, v_k_1991_);
lean_closure_set(v___f_2002_, 1, v___y_1994_);
lean_closure_set(v___f_2002_, 2, v___y_1995_);
lean_closure_set(v___f_2002_, 3, v___y_1996_);
v___x_2003_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1988_, v_type_1989_, v_val_1990_, v___f_2002_, v_nondep_1992_, v_kind_1993_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2003_) == 0)
{
return v___x_2003_;
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2012_, lean_object* v_type_2013_, lean_object* v_val_2014_, lean_object* v_k_2015_, lean_object* v_nondep_2016_, lean_object* v_kind_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
uint8_t v_nondep_boxed_2026_; uint8_t v_kind_boxed_2027_; lean_object* v_res_2028_; 
v_nondep_boxed_2026_ = lean_unbox(v_nondep_2016_);
v_kind_boxed_2027_ = lean_unbox(v_kind_2017_);
v_res_2028_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2012_, v_type_2013_, v_val_2014_, v_k_2015_, v_nondep_boxed_2026_, v_kind_boxed_2027_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = l_Lean_instInhabitedExpr;
v___x_2031_ = lean_panic_fn_borrowed(v___x_2030_, v_msg_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2032_, lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_box(0);
return v___x_2034_;
}
else
{
lean_object* v_key_2035_; lean_object* v_value_2036_; lean_object* v_tail_2037_; uint8_t v___x_2038_; 
v_key_2035_ = lean_ctor_get(v_x_2033_, 0);
v_value_2036_ = lean_ctor_get(v_x_2033_, 1);
v_tail_2037_ = lean_ctor_get(v_x_2033_, 2);
v___x_2038_ = l_Lean_ExprStructEq_beq(v_key_2035_, v_a_2032_);
if (v___x_2038_ == 0)
{
v_x_2033_ = v_tail_2037_;
goto _start;
}
else
{
lean_object* v___x_2040_; 
lean_inc(v_value_2036_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_value_2036_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2041_, lean_object* v_x_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2041_, v_x_2042_);
lean_dec(v_x_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_buckets_2046_; lean_object* v___x_2047_; uint64_t v___x_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; uint64_t v_fold_2051_; uint64_t v___x_2052_; uint64_t v___x_2053_; uint64_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_buckets_2046_ = lean_ctor_get(v_m_2044_, 1);
v___x_2047_ = lean_array_get_size(v_buckets_2046_);
v___x_2048_ = l_Lean_ExprStructEq_hash(v_a_2045_);
v___x_2049_ = 32ULL;
v___x_2050_ = lean_uint64_shift_right(v___x_2048_, v___x_2049_);
v_fold_2051_ = lean_uint64_xor(v___x_2048_, v___x_2050_);
v___x_2052_ = 16ULL;
v___x_2053_ = lean_uint64_shift_right(v_fold_2051_, v___x_2052_);
v___x_2054_ = lean_uint64_xor(v_fold_2051_, v___x_2053_);
v___x_2055_ = lean_uint64_to_usize(v___x_2054_);
v___x_2056_ = lean_usize_of_nat(v___x_2047_);
v___x_2057_ = ((size_t)1ULL);
v___x_2058_ = lean_usize_sub(v___x_2056_, v___x_2057_);
v___x_2059_ = lean_usize_land(v___x_2055_, v___x_2058_);
v___x_2060_ = lean_array_uget_borrowed(v_buckets_2046_, v___x_2059_);
v___x_2061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2045_, v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2062_, v_a_2063_);
lean_dec_ref(v_a_2063_);
lean_dec_ref(v_m_2062_);
return v_res_2064_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
uint8_t v___x_2067_; 
v___x_2067_ = 0;
return v___x_2067_;
}
else
{
lean_object* v_key_2068_; lean_object* v_tail_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v_fst_2072_; lean_object* v_snd_2073_; uint8_t v___x_2077_; 
v_key_2068_ = lean_ctor_get(v_x_2066_, 0);
v_tail_2069_ = lean_ctor_get(v_x_2066_, 2);
v_fst_2070_ = lean_ctor_get(v_key_2068_, 0);
v_snd_2071_ = lean_ctor_get(v_key_2068_, 1);
v_fst_2072_ = lean_ctor_get(v_a_2065_, 0);
v_snd_2073_ = lean_ctor_get(v_a_2065_, 1);
v___x_2077_ = lean_unbox(v_fst_2072_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2078_; 
v___x_2078_ = lean_unbox(v_fst_2070_);
if (v___x_2078_ == 0)
{
goto v___jp_2074_;
}
else
{
v_x_2066_ = v_tail_2069_;
goto _start;
}
}
else
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_unbox(v_fst_2070_);
if (v___x_2080_ == 0)
{
v_x_2066_ = v_tail_2069_;
goto _start;
}
else
{
goto v___jp_2074_;
}
}
v___jp_2074_:
{
uint8_t v___x_2075_; 
v___x_2075_ = l_Lean_ExprStructEq_beq(v_snd_2071_, v_snd_2073_);
if (v___x_2075_ == 0)
{
v_x_2066_ = v_tail_2069_;
goto _start;
}
else
{
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2082_, lean_object* v_x_2083_){
_start:
{
uint8_t v_res_2084_; lean_object* v_r_2085_; 
v_res_2084_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2082_, v_x_2083_);
lean_dec(v_x_2083_);
lean_dec_ref(v_a_2082_);
v_r_2085_ = lean_box(v_res_2084_);
return v_r_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2086_, lean_object* v_b_2087_, lean_object* v_x_2088_){
_start:
{
if (lean_obj_tag(v_x_2088_) == 0)
{
lean_dec(v_b_2087_);
lean_dec_ref(v_a_2086_);
return v_x_2088_;
}
else
{
lean_object* v_key_2089_; lean_object* v_value_2090_; lean_object* v_tail_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2110_; 
v_key_2089_ = lean_ctor_get(v_x_2088_, 0);
v_value_2090_ = lean_ctor_get(v_x_2088_, 1);
v_tail_2091_ = lean_ctor_get(v_x_2088_, 2);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2088_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2093_ = v_x_2088_;
v_isShared_2094_ = v_isSharedCheck_2110_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_tail_2091_);
lean_inc(v_value_2090_);
lean_inc(v_key_2089_);
lean_dec(v_x_2088_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2110_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v_fst_2102_; lean_object* v_snd_2103_; uint8_t v___x_2107_; 
v_fst_2100_ = lean_ctor_get(v_key_2089_, 0);
v_snd_2101_ = lean_ctor_get(v_key_2089_, 1);
v_fst_2102_ = lean_ctor_get(v_a_2086_, 0);
v_snd_2103_ = lean_ctor_get(v_a_2086_, 1);
v___x_2107_ = lean_unbox(v_fst_2102_);
if (v___x_2107_ == 0)
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_unbox(v_fst_2100_);
if (v___x_2108_ == 0)
{
goto v___jp_2104_;
}
else
{
goto v___jp_2095_;
}
}
else
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_unbox(v_fst_2100_);
if (v___x_2109_ == 0)
{
goto v___jp_2095_;
}
else
{
goto v___jp_2104_;
}
}
v___jp_2095_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2086_, v_b_2087_, v_tail_2091_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 2, v___x_2096_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_key_2089_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_value_2090_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
v___jp_2104_:
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Lean_ExprStructEq_beq(v_snd_2101_, v_snd_2103_);
if (v___x_2105_ == 0)
{
goto v___jp_2095_;
}
else
{
lean_object* v___x_2106_; 
lean_del_object(v___x_2093_);
lean_dec(v_value_2090_);
lean_dec(v_key_2089_);
v___x_2106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2086_);
lean_ctor_set(v___x_2106_, 1, v_b_2087_);
lean_ctor_set(v___x_2106_, 2, v_tail_2091_);
return v___x_2106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
return v_x_2111_;
}
else
{
lean_object* v_key_2113_; lean_object* v_value_2114_; lean_object* v_tail_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2146_; 
v_key_2113_ = lean_ctor_get(v_x_2112_, 0);
v_value_2114_ = lean_ctor_get(v_x_2112_, 1);
v_tail_2115_ = lean_ctor_get(v_x_2112_, 2);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_x_2112_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2117_ = v_x_2112_;
v_isShared_2118_ = v_isSharedCheck_2146_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_tail_2115_);
lean_inc(v_value_2114_);
lean_inc(v_key_2113_);
lean_dec(v_x_2112_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2146_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v___x_2121_; uint64_t v___y_2123_; uint8_t v___x_2143_; 
v_fst_2119_ = lean_ctor_get(v_key_2113_, 0);
v_snd_2120_ = lean_ctor_get(v_key_2113_, 1);
v___x_2121_ = lean_array_get_size(v_x_2111_);
v___x_2143_ = lean_unbox(v_fst_2119_);
if (v___x_2143_ == 0)
{
uint64_t v___x_2144_; 
v___x_2144_ = 13ULL;
v___y_2123_ = v___x_2144_;
goto v___jp_2122_;
}
else
{
uint64_t v___x_2145_; 
v___x_2145_ = 11ULL;
v___y_2123_ = v___x_2145_;
goto v___jp_2122_;
}
v___jp_2122_:
{
uint64_t v___x_2124_; uint64_t v___x_2125_; uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v_fold_2128_; uint64_t v___x_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2124_ = l_Lean_ExprStructEq_hash(v_snd_2120_);
v___x_2125_ = lean_uint64_mix_hash(v___y_2123_, v___x_2124_);
v___x_2126_ = 32ULL;
v___x_2127_ = lean_uint64_shift_right(v___x_2125_, v___x_2126_);
v_fold_2128_ = lean_uint64_xor(v___x_2125_, v___x_2127_);
v___x_2129_ = 16ULL;
v___x_2130_ = lean_uint64_shift_right(v_fold_2128_, v___x_2129_);
v___x_2131_ = lean_uint64_xor(v_fold_2128_, v___x_2130_);
v___x_2132_ = lean_uint64_to_usize(v___x_2131_);
v___x_2133_ = lean_usize_of_nat(v___x_2121_);
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_sub(v___x_2133_, v___x_2134_);
v___x_2136_ = lean_usize_land(v___x_2132_, v___x_2135_);
v___x_2137_ = lean_array_uget_borrowed(v_x_2111_, v___x_2136_);
lean_inc(v___x_2137_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 2, v___x_2137_);
v___x_2139_ = v___x_2117_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_key_2113_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_value_2114_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_array_uset(v_x_2111_, v___x_2136_, v___x_2139_);
v_x_2111_ = v___x_2140_;
v_x_2112_ = v_tail_2115_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2147_, lean_object* v_source_2148_, lean_object* v_target_2149_){
_start:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_array_get_size(v_source_2148_);
v___x_2151_ = lean_nat_dec_lt(v_i_2147_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec_ref(v_source_2148_);
lean_dec(v_i_2147_);
return v_target_2149_;
}
else
{
lean_object* v_es_2152_; lean_object* v___x_2153_; lean_object* v_source_2154_; lean_object* v_target_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_es_2152_ = lean_array_fget(v_source_2148_, v_i_2147_);
v___x_2153_ = lean_box(0);
v_source_2154_ = lean_array_fset(v_source_2148_, v_i_2147_, v___x_2153_);
v_target_2155_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2149_, v_es_2152_);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_nat_add(v_i_2147_, v___x_2156_);
lean_dec(v_i_2147_);
v_i_2147_ = v___x_2157_;
v_source_2148_ = v_source_2154_;
v_target_2149_ = v_target_2155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v_nbuckets_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2160_ = lean_array_get_size(v_data_2159_);
v___x_2161_ = lean_unsigned_to_nat(2u);
v_nbuckets_2162_ = lean_nat_mul(v___x_2160_, v___x_2161_);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_mk_array(v_nbuckets_2162_, v___x_2164_);
v___x_2166_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2163_, v_data_2159_, v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2167_, lean_object* v_a_2168_, lean_object* v_b_2169_){
_start:
{
lean_object* v_size_2170_; lean_object* v_buckets_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2222_; 
v_size_2170_ = lean_ctor_get(v_m_2167_, 0);
v_buckets_2171_ = lean_ctor_get(v_m_2167_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_m_2167_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2173_ = v_m_2167_;
v_isShared_2174_ = v_isSharedCheck_2222_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_buckets_2171_);
lean_inc(v_size_2170_);
lean_dec(v_m_2167_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2222_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v___x_2177_; uint64_t v___y_2179_; uint8_t v___x_2219_; 
v_fst_2175_ = lean_ctor_get(v_a_2168_, 0);
v_snd_2176_ = lean_ctor_get(v_a_2168_, 1);
v___x_2177_ = lean_array_get_size(v_buckets_2171_);
v___x_2219_ = lean_unbox(v_fst_2175_);
if (v___x_2219_ == 0)
{
uint64_t v___x_2220_; 
v___x_2220_ = 13ULL;
v___y_2179_ = v___x_2220_;
goto v___jp_2178_;
}
else
{
uint64_t v___x_2221_; 
v___x_2221_ = 11ULL;
v___y_2179_ = v___x_2221_;
goto v___jp_2178_;
}
v___jp_2178_:
{
uint64_t v___x_2180_; uint64_t v___x_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v_fold_2184_; uint64_t v___x_2185_; uint64_t v___x_2186_; uint64_t v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; lean_object* v_bkt_2193_; uint8_t v___x_2194_; 
v___x_2180_ = l_Lean_ExprStructEq_hash(v_snd_2176_);
v___x_2181_ = lean_uint64_mix_hash(v___y_2179_, v___x_2180_);
v___x_2182_ = 32ULL;
v___x_2183_ = lean_uint64_shift_right(v___x_2181_, v___x_2182_);
v_fold_2184_ = lean_uint64_xor(v___x_2181_, v___x_2183_);
v___x_2185_ = 16ULL;
v___x_2186_ = lean_uint64_shift_right(v_fold_2184_, v___x_2185_);
v___x_2187_ = lean_uint64_xor(v_fold_2184_, v___x_2186_);
v___x_2188_ = lean_uint64_to_usize(v___x_2187_);
v___x_2189_ = lean_usize_of_nat(v___x_2177_);
v___x_2190_ = ((size_t)1ULL);
v___x_2191_ = lean_usize_sub(v___x_2189_, v___x_2190_);
v___x_2192_ = lean_usize_land(v___x_2188_, v___x_2191_);
v_bkt_2193_ = lean_array_uget_borrowed(v_buckets_2171_, v___x_2192_);
v___x_2194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2168_, v_bkt_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v_size_x27_2196_; lean_object* v___x_2197_; lean_object* v_buckets_x27_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2195_ = lean_unsigned_to_nat(1u);
v_size_x27_2196_ = lean_nat_add(v_size_2170_, v___x_2195_);
lean_dec(v_size_2170_);
lean_inc(v_bkt_2193_);
v___x_2197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2168_);
lean_ctor_set(v___x_2197_, 1, v_b_2169_);
lean_ctor_set(v___x_2197_, 2, v_bkt_2193_);
v_buckets_x27_2198_ = lean_array_uset(v_buckets_2171_, v___x_2192_, v___x_2197_);
v___x_2199_ = lean_unsigned_to_nat(4u);
v___x_2200_ = lean_nat_mul(v_size_x27_2196_, v___x_2199_);
v___x_2201_ = lean_unsigned_to_nat(3u);
v___x_2202_ = lean_nat_div(v___x_2200_, v___x_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_array_get_size(v_buckets_x27_2198_);
v___x_2204_ = lean_nat_dec_le(v___x_2202_, v___x_2203_);
lean_dec(v___x_2202_);
if (v___x_2204_ == 0)
{
lean_object* v_val_2205_; lean_object* v___x_2207_; 
v_val_2205_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2198_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_val_2205_);
lean_ctor_set(v___x_2173_, 0, v_size_x27_2196_);
v___x_2207_ = v___x_2173_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_size_x27_2196_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_val_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
else
{
lean_object* v___x_2210_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_buckets_x27_2198_);
lean_ctor_set(v___x_2173_, 0, v_size_x27_2196_);
v___x_2210_ = v___x_2173_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_size_x27_2196_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_buckets_x27_2198_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v___x_2212_; lean_object* v_buckets_x27_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_inc(v_bkt_2193_);
v___x_2212_ = lean_box(0);
v_buckets_x27_2213_ = lean_array_uset(v_buckets_2171_, v___x_2192_, v___x_2212_);
v___x_2214_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2168_, v_b_2169_, v_bkt_2193_);
v___x_2215_ = lean_array_uset(v_buckets_x27_2213_, v___x_2192_, v___x_2214_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v___x_2215_);
v___x_2217_ = v___x_2173_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_size_2170_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2223_, lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_box(0);
return v___x_2225_;
}
else
{
lean_object* v_key_2226_; lean_object* v_value_2227_; lean_object* v_tail_2228_; lean_object* v_fst_2229_; lean_object* v_snd_2230_; lean_object* v_fst_2231_; lean_object* v_snd_2232_; uint8_t v___x_2237_; 
v_key_2226_ = lean_ctor_get(v_x_2224_, 0);
v_value_2227_ = lean_ctor_get(v_x_2224_, 1);
v_tail_2228_ = lean_ctor_get(v_x_2224_, 2);
v_fst_2229_ = lean_ctor_get(v_key_2226_, 0);
v_snd_2230_ = lean_ctor_get(v_key_2226_, 1);
v_fst_2231_ = lean_ctor_get(v_a_2223_, 0);
v_snd_2232_ = lean_ctor_get(v_a_2223_, 1);
v___x_2237_ = lean_unbox(v_fst_2231_);
if (v___x_2237_ == 0)
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_unbox(v_fst_2229_);
if (v___x_2238_ == 0)
{
goto v___jp_2233_;
}
else
{
v_x_2224_ = v_tail_2228_;
goto _start;
}
}
else
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_unbox(v_fst_2229_);
if (v___x_2240_ == 0)
{
v_x_2224_ = v_tail_2228_;
goto _start;
}
else
{
goto v___jp_2233_;
}
}
v___jp_2233_:
{
uint8_t v___x_2234_; 
v___x_2234_ = l_Lean_ExprStructEq_beq(v_snd_2230_, v_snd_2232_);
if (v___x_2234_ == 0)
{
v_x_2224_ = v_tail_2228_;
goto _start;
}
else
{
lean_object* v___x_2236_; 
lean_inc(v_value_2227_);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_value_2227_);
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2242_, v_x_2243_);
lean_dec(v_x_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_buckets_2247_; lean_object* v_fst_2248_; lean_object* v_snd_2249_; lean_object* v___x_2250_; uint64_t v___y_2252_; uint8_t v___x_2268_; 
v_buckets_2247_ = lean_ctor_get(v_m_2245_, 1);
v_fst_2248_ = lean_ctor_get(v_a_2246_, 0);
v_snd_2249_ = lean_ctor_get(v_a_2246_, 1);
v___x_2250_ = lean_array_get_size(v_buckets_2247_);
v___x_2268_ = lean_unbox(v_fst_2248_);
if (v___x_2268_ == 0)
{
uint64_t v___x_2269_; 
v___x_2269_ = 13ULL;
v___y_2252_ = v___x_2269_;
goto v___jp_2251_;
}
else
{
uint64_t v___x_2270_; 
v___x_2270_ = 11ULL;
v___y_2252_ = v___x_2270_;
goto v___jp_2251_;
}
v___jp_2251_:
{
uint64_t v___x_2253_; uint64_t v___x_2254_; uint64_t v___x_2255_; uint64_t v___x_2256_; uint64_t v_fold_2257_; uint64_t v___x_2258_; uint64_t v___x_2259_; uint64_t v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2253_ = l_Lean_ExprStructEq_hash(v_snd_2249_);
v___x_2254_ = lean_uint64_mix_hash(v___y_2252_, v___x_2253_);
v___x_2255_ = 32ULL;
v___x_2256_ = lean_uint64_shift_right(v___x_2254_, v___x_2255_);
v_fold_2257_ = lean_uint64_xor(v___x_2254_, v___x_2256_);
v___x_2258_ = 16ULL;
v___x_2259_ = lean_uint64_shift_right(v_fold_2257_, v___x_2258_);
v___x_2260_ = lean_uint64_xor(v_fold_2257_, v___x_2259_);
v___x_2261_ = lean_uint64_to_usize(v___x_2260_);
v___x_2262_ = lean_usize_of_nat(v___x_2250_);
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_sub(v___x_2262_, v___x_2263_);
v___x_2265_ = lean_usize_land(v___x_2261_, v___x_2264_);
v___x_2266_ = lean_array_uget_borrowed(v_buckets_2247_, v___x_2265_);
v___x_2267_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2246_, v___x_2266_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2271_, v_a_2272_);
lean_dec_ref(v_a_2272_);
lean_dec_ref(v_m_2271_);
return v_res_2273_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2274_; lean_object* v_dummy_2275_; 
v___x_2274_ = lean_box(0);
v_dummy_2275_ = l_Lean_Expr_sort___override(v___x_2274_);
return v_dummy_2275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2276_, lean_object* v_fst_2277_, lean_object* v_fvars_2278_, lean_object* v_a_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_a_2290_; uint8_t v___x_2294_; 
v___x_2294_ = lean_nat_dec_lt(v_a_2279_, v_upperBound_2276_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v_a_2279_);
lean_dec(v_fvars_2278_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v_b_2280_);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v_binderInfo_2298_; uint8_t v___x_2299_; 
v___x_2296_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2297_ = lean_array_get_borrowed(v___x_2296_, v_fst_2277_, v_a_2279_);
v_binderInfo_2298_ = lean_ctor_get_uint8(v___x_2297_, sizeof(void*)*2);
v___x_2299_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2298_);
if (v___x_2299_ == 0)
{
v_a_2290_ = v_b_2280_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = l_Lean_instInhabitedExpr;
v___x_2301_ = 0;
v___x_2302_ = lean_array_get_borrowed(v___x_2300_, v_b_2280_, v_a_2279_);
lean_inc(v___x_2302_);
lean_inc(v_fvars_2278_);
v___x_2303_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2278_, v___x_2302_, v___x_2301_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = lean_array_set(v_b_2280_, v_a_2279_, v_a_2304_);
v_a_2290_ = v___x_2305_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_b_2280_);
lean_dec(v_a_2279_);
lean_dec(v_fvars_2278_);
v_a_2306_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2303_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2303_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
v___jp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = lean_nat_add(v_a_2279_, v___x_2291_);
lean_dec(v_a_2279_);
v_a_2279_ = v___x_2292_;
v_b_2280_ = v_a_2290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2314_, size_t v_sz_2315_, size_t v_i_2316_, lean_object* v_bs_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_lt(v_i_2316_, v_sz_2315_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_dec(v_fvars_2314_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_bs_2317_);
return v___x_2327_;
}
else
{
uint8_t v___x_2328_; lean_object* v_v_2329_; lean_object* v___x_2330_; 
v___x_2328_ = 0;
v_v_2329_ = lean_array_uget_borrowed(v_bs_2317_, v_i_2316_);
lean_inc(v_v_2329_);
lean_inc(v_fvars_2314_);
v___x_2330_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2314_, v_v_2329_, v___x_2328_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; lean_object* v_bs_x27_2333_; size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = lean_unsigned_to_nat(0u);
v_bs_x27_2333_ = lean_array_uset(v_bs_2317_, v_i_2316_, v___x_2332_);
v___x_2334_ = ((size_t)1ULL);
v___x_2335_ = lean_usize_add(v_i_2316_, v___x_2334_);
v___x_2336_ = lean_array_uset(v_bs_x27_2333_, v_i_2316_, v_a_2331_);
v_i_2316_ = v___x_2335_;
v_bs_2317_ = v___x_2336_;
goto _start;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_bs_2317_);
lean_dec(v_fvars_2314_);
v_a_2338_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2330_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2330_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2346_, lean_object* v_f_2347_, lean_object* v_args_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
uint8_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = 0;
lean_inc_ref(v_f_2347_);
lean_inc(v_fvars_2346_);
v___x_2358_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2346_, v_f_2347_, v___x_2357_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2358_) == 0)
{
uint8_t v_implicits_2359_; 
v_implicits_2359_ = lean_ctor_get_uint8(v_a_2349_, 2);
if (v_implicits_2359_ == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; 
v_a_2360_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2358_, 1);
lean_inc(v_a_2355_);
lean_inc_ref(v_a_2354_);
lean_inc(v_a_2353_);
lean_inc_ref(v_a_2352_);
v___x_2361_ = lean_infer_type(v_f_2347_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2362_, v_args_2348_, v___x_2357_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v_fst_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v_fst_2365_ = lean_ctor_get(v_a_2364_, 0);
lean_inc(v_fst_2365_);
lean_dec(v_a_2364_);
v___x_2366_ = lean_array_get_size(v_args_2348_);
v___x_2367_ = lean_unsigned_to_nat(0u);
v___x_2368_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2366_, v_fst_2365_, v_fvars_2346_, v___x_2367_, v_args_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_fst_2365_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2377_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2373_ = l_Lean_mkAppN(v_a_2360_, v_a_2369_);
lean_dec(v_a_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2373_);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_a_2360_);
v_a_2378_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2368_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2368_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_a_2360_);
lean_dec_ref(v_args_2348_);
lean_dec(v_fvars_2346_);
v_a_2386_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2363_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2363_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_dec(v_a_2360_);
lean_dec_ref(v_args_2348_);
lean_dec(v_fvars_2346_);
return v___x_2361_;
}
}
else
{
lean_object* v_a_2394_; size_t v_sz_2395_; size_t v___x_2396_; lean_object* v___x_2397_; 
lean_dec_ref(v_f_2347_);
v_a_2394_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2358_, 1);
v_sz_2395_ = lean_array_size(v_args_2348_);
v___x_2396_ = ((size_t)0ULL);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2346_, v_sz_2395_, v___x_2396_, v_args_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = l_Lean_mkAppN(v_a_2394_, v_a_2398_);
lean_dec(v_a_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec(v_a_2394_);
v_a_2407_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2397_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2397_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2348_);
lean_dec_ref(v_f_2347_);
lean_dec(v_fvars_2346_);
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2415_, lean_object* v_f_2416_, lean_object* v_args_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2415_, v_f_2416_, v_args_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2427_, lean_object* v_b_2428_, uint8_t v___x_2429_, lean_object* v_mk_2430_, lean_object* v_a_2431_, lean_object* v_x_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_inc_ref(v_x_2432_);
v___x_2441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_x_2432_);
lean_ctor_set(v___x_2441_, 1, v_fvars_2427_);
v___x_2442_ = lean_expr_instantiate1(v_b_2428_, v_x_2432_);
v___x_2443_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2441_, v___x_2442_, v___x_2429_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2443_) == 0)
{
uint8_t v_lift_2444_; 
v_lift_2444_ = lean_ctor_get_uint8(v___y_2433_, 10);
if (v_lift_2444_ == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2457_; 
v_a_2445_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2447_ = v___x_2443_;
v_isShared_2448_ = v_isSharedCheck_2457_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2443_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2457_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2449_ = lean_unsigned_to_nat(1u);
v___x_2450_ = lean_mk_empty_array_with_capacity(v___x_2449_);
v___x_2451_ = lean_array_push(v___x_2450_, v_x_2432_);
v___x_2452_ = lean_expr_abstract(v_a_2445_, v___x_2451_);
lean_dec_ref(v___x_2451_);
lean_dec(v_a_2445_);
v___x_2453_ = lean_apply_2(v_mk_2430_, v_a_2431_, v___x_2452_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2453_);
v___x_2455_ = v___x_2447_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2458_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2459_ = l_Lean_Expr_fvarId_x21(v_x_2432_);
v___x_2460_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2459_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2474_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2474_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2474_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2465_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2461_, v_a_2458_);
lean_dec(v_a_2461_);
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_mk_empty_array_with_capacity(v___x_2466_);
v___x_2468_ = lean_array_push(v___x_2467_, v_x_2432_);
v___x_2469_ = lean_expr_abstract(v___x_2465_, v___x_2468_);
lean_dec_ref(v___x_2468_);
lean_dec_ref(v___x_2465_);
v___x_2470_ = lean_apply_2(v_mk_2430_, v_a_2431_, v___x_2469_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2470_);
v___x_2472_ = v___x_2463_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_a_2458_);
lean_dec_ref(v_x_2432_);
lean_dec_ref(v_a_2431_);
lean_dec_ref(v_mk_2430_);
v_a_2475_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2460_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2460_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2432_);
lean_dec_ref(v_a_2431_);
lean_dec_ref(v_mk_2430_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2483_, lean_object* v_b_2484_, lean_object* v___x_2485_, lean_object* v_mk_2486_, lean_object* v_a_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v___x_41952__boxed_2497_; lean_object* v_res_2498_; 
v___x_41952__boxed_2497_ = lean_unbox(v___x_2485_);
v_res_2498_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2483_, v_b_2484_, v___x_41952__boxed_2497_, v_mk_2486_, v_a_2487_, v_x_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v_b_2484_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2499_, lean_object* v_n_2500_, lean_object* v_t_2501_, lean_object* v_b_2502_, uint8_t v_i_2503_, lean_object* v_mk_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
uint8_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = 0;
lean_inc(v_fvars_2499_);
v___x_2514_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2499_, v_t_2501_, v___x_2513_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
if (lean_obj_tag(v___x_2514_) == 0)
{
uint8_t v_underBinder_2515_; 
v_underBinder_2515_ = lean_ctor_get_uint8(v_a_2505_, 4);
if (v_underBinder_2515_ == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_n_2500_);
lean_dec(v_fvars_2499_);
v_a_2516_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2518_ = v___x_2514_;
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2514_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = lean_apply_2(v_mk_2504_, v_a_2516_, v_b_2502_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; 
v_a_2525_ = lean_ctor_get(v___x_2514_, 0);
lean_inc_n(v_a_2525_, 2);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2526_ = lean_box(v___x_2513_);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2527_, 0, v_fvars_2499_);
lean_closure_set(v___f_2527_, 1, v_b_2502_);
lean_closure_set(v___f_2527_, 2, v___x_2526_);
lean_closure_set(v___f_2527_, 3, v_mk_2504_);
lean_closure_set(v___f_2527_, 4, v_a_2525_);
v___x_2528_ = 0;
v___x_2529_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2500_, v_i_2503_, v_a_2525_, v___f_2527_, v___x_2528_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2529_;
}
}
else
{
lean_dec_ref(v_mk_2504_);
lean_dec_ref(v_b_2502_);
lean_dec(v_n_2500_);
lean_dec(v_fvars_2499_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2530_, lean_object* v_n_2531_, lean_object* v_t_2532_, lean_object* v_b_2533_, lean_object* v_i_2534_, lean_object* v_mk_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
uint8_t v_i_boxed_2544_; lean_object* v_res_2545_; 
v_i_boxed_2544_ = lean_unbox(v_i_2534_);
v_res_2545_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2530_, v_n_2531_, v_t_2532_, v_b_2533_, v_i_boxed_2544_, v_mk_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2546_, lean_object* v_e_2547_, lean_object* v_topLevel_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
uint8_t v_topLevel_boxed_2557_; lean_object* v_res_2558_; 
v_topLevel_boxed_2557_ = lean_unbox(v_topLevel_2548_);
v_res_2558_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2546_, v_e_2547_, v_topLevel_boxed_2557_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2563_ = lean_unsigned_to_nat(27u);
v___x_2564_ = lean_unsigned_to_nat(1964u);
v___x_2565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2567_ = l_mkPanicMessageWithDecl(v___x_2566_, v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2568_, lean_object* v_fvars_2569_, lean_object* v_b_2570_, uint8_t v___x_2571_, lean_object* v_e_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, uint8_t v_isLet_2575_, uint8_t v_topLevel_2576_, lean_object* v_x_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
if (v_fst_2568_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_inc_ref(v_x_2577_);
v___x_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_x_2577_);
lean_ctor_set(v___x_2586_, 1, v_fvars_2569_);
v___x_2587_ = lean_expr_instantiate1(v_b_2570_, v_x_2577_);
v___x_2588_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2586_, v___x_2587_, v___x_2571_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2588_) == 0)
{
if (lean_obj_tag(v_e_2572_) == 8)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2626_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2626_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2626_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_declName_2593_; lean_object* v_type_2594_; lean_object* v_value_2595_; lean_object* v_body_2596_; uint8_t v_nondep_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; uint8_t v___x_2604_; 
v_declName_2593_ = lean_ctor_get(v_e_2572_, 0);
v_type_2594_ = lean_ctor_get(v_e_2572_, 1);
v_value_2595_ = lean_ctor_get(v_e_2572_, 2);
v_body_2596_ = lean_ctor_get(v_e_2572_, 3);
v_nondep_2597_ = lean_ctor_get_uint8(v_e_2572_, sizeof(void*)*4 + 8);
v___x_2598_ = lean_unsigned_to_nat(1u);
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2598_);
v___x_2600_ = lean_array_push(v___x_2599_, v_x_2577_);
v___x_2601_ = lean_expr_abstract(v_a_2589_, v___x_2600_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2589_);
v___x_2602_ = lean_ptr_addr(v_type_2594_);
v___x_2603_ = lean_ptr_addr(v_a_2573_);
v___x_2604_ = lean_usize_dec_eq(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
lean_inc(v_declName_2593_);
lean_dec_ref_known(v_e_2572_, 4);
v___x_2605_ = l_Lean_Expr_letE___override(v_declName_2593_, v_a_2573_, v_a_2574_, v___x_2601_, v_nondep_2597_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2605_);
v___x_2607_ = v___x_2591_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; uint8_t v___x_2611_; 
v___x_2609_ = lean_ptr_addr(v_value_2595_);
v___x_2610_ = lean_ptr_addr(v_a_2574_);
v___x_2611_ = lean_usize_dec_eq(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_inc(v_declName_2593_);
lean_dec_ref_known(v_e_2572_, 4);
v___x_2612_ = l_Lean_Expr_letE___override(v_declName_2593_, v_a_2573_, v_a_2574_, v___x_2601_, v_nondep_2597_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2612_);
v___x_2614_ = v___x_2591_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
else
{
size_t v___x_2616_; size_t v___x_2617_; uint8_t v___x_2618_; 
v___x_2616_ = lean_ptr_addr(v_body_2596_);
v___x_2617_ = lean_ptr_addr(v___x_2601_);
v___x_2618_ = lean_usize_dec_eq(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_inc(v_declName_2593_);
lean_dec_ref_known(v_e_2572_, 4);
v___x_2619_ = l_Lean_Expr_letE___override(v_declName_2593_, v_a_2573_, v_a_2574_, v___x_2601_, v_nondep_2597_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2619_);
v___x_2621_ = v___x_2591_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2624_; 
lean_dec_ref(v___x_2601_);
lean_dec_ref(v_a_2574_);
lean_dec_ref(v_a_2573_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_e_2572_);
v___x_2624_ = v___x_2591_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_e_2572_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
}
else
{
lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v_x_2577_);
lean_dec_ref(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec_ref(v_e_2572_);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v___x_2588_, 0);
lean_dec(v_unused_2636_);
v___x_2628_ = v___x_2588_;
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
else
{
lean_dec(v___x_2588_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2631_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2630_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2631_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_dec_ref(v_x_2577_);
lean_dec_ref(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec_ref(v_e_2572_);
return v___x_2588_;
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec_ref(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec_ref(v_e_2572_);
v___x_2637_ = l_Lean_Expr_fvarId_x21(v_x_2577_);
v___x_2638_ = l_Lean_FVarId_getDecl___redArg(v___x_2637_, v___y_2581_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2639_, v_isLet_2575_, v___y_2578_, v___y_2580_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref_known(v___x_2640_, 1);
v___x_2641_ = lean_expr_instantiate1(v_b_2570_, v_x_2577_);
lean_dec_ref(v_x_2577_);
v___x_2642_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2569_, v___x_2641_, v_topLevel_2576_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
return v___x_2642_;
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_x_2577_);
lean_dec(v_fvars_2569_);
v_a_2643_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2640_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2640_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v_x_2577_);
lean_dec(v_fvars_2569_);
v_a_2651_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2638_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2638_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2659_ = _args[0];
lean_object* v_fvars_2660_ = _args[1];
lean_object* v_b_2661_ = _args[2];
lean_object* v___x_2662_ = _args[3];
lean_object* v_e_2663_ = _args[4];
lean_object* v_a_2664_ = _args[5];
lean_object* v_a_2665_ = _args[6];
lean_object* v_isLet_2666_ = _args[7];
lean_object* v_topLevel_2667_ = _args[8];
lean_object* v_x_2668_ = _args[9];
lean_object* v___y_2669_ = _args[10];
lean_object* v___y_2670_ = _args[11];
lean_object* v___y_2671_ = _args[12];
lean_object* v___y_2672_ = _args[13];
lean_object* v___y_2673_ = _args[14];
lean_object* v___y_2674_ = _args[15];
lean_object* v___y_2675_ = _args[16];
lean_object* v___y_2676_ = _args[17];
_start:
{
uint8_t v_fst_42097__boxed_2677_; uint8_t v___x_42098__boxed_2678_; uint8_t v_isLet_boxed_2679_; uint8_t v_topLevel_boxed_2680_; lean_object* v_res_2681_; 
v_fst_42097__boxed_2677_ = lean_unbox(v_fst_2659_);
v___x_42098__boxed_2678_ = lean_unbox(v___x_2662_);
v_isLet_boxed_2679_ = lean_unbox(v_isLet_2666_);
v_topLevel_boxed_2680_ = lean_unbox(v_topLevel_2667_);
v_res_2681_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_42097__boxed_2677_, v_fvars_2660_, v_b_2661_, v___x_42098__boxed_2678_, v_e_2663_, v_a_2664_, v_a_2665_, v_isLet_boxed_2679_, v_topLevel_boxed_2680_, v_x_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec_ref(v_b_2661_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2682_, lean_object* v_e_2683_, uint8_t v_isLet_2684_, lean_object* v_n_2685_, lean_object* v_t_2686_, lean_object* v_v_2687_, lean_object* v_b_2688_, uint8_t v_topLevel_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; uint8_t v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = 0;
lean_inc(v_fvars_2682_);
v___x_2713_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2682_, v_t_2686_, v___x_2712_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
lean_inc(v_fvars_2682_);
v___x_2715_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2682_, v_v_2687_, v___x_2712_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2827_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2827_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2827_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; uint8_t v_descend_2767_; uint8_t v_underBinder_2768_; uint8_t v_usedOnly_2769_; uint8_t v_merge_2770_; uint8_t v_lift_2771_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; uint8_t v___y_2809_; 
v_descend_2767_ = lean_ctor_get_uint8(v_a_2690_, 3);
v_underBinder_2768_ = lean_ctor_get_uint8(v_a_2690_, 4);
v_usedOnly_2769_ = lean_ctor_get_uint8(v_a_2690_, 5);
v_merge_2770_ = lean_ctor_get_uint8(v_a_2690_, 6);
v_lift_2771_ = lean_ctor_get_uint8(v_a_2690_, 10);
if (v_usedOnly_2769_ == 0)
{
v___y_2809_ = v___x_2712_;
goto v___jp_2808_;
}
else
{
uint8_t v___x_2825_; 
v___x_2825_ = l_Lean_Expr_hasLooseBVars(v_b_2688_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
lean_del_object(v___x_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2714_);
lean_dec(v_n_2685_);
lean_dec_ref(v_e_2683_);
v___x_2826_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2682_, v_b_2688_, v_topLevel_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2826_;
}
else
{
v___y_2809_ = v___x_2712_;
goto v___jp_2808_;
}
}
v___jp_2720_:
{
if (lean_obj_tag(v_e_2683_) == 8)
{
lean_object* v_declName_2721_; lean_object* v_type_2722_; lean_object* v_value_2723_; lean_object* v_body_2724_; uint8_t v_nondep_2725_; size_t v___x_2726_; size_t v___x_2727_; uint8_t v___x_2728_; 
v_declName_2721_ = lean_ctor_get(v_e_2683_, 0);
v_type_2722_ = lean_ctor_get(v_e_2683_, 1);
v_value_2723_ = lean_ctor_get(v_e_2683_, 2);
v_body_2724_ = lean_ctor_get(v_e_2683_, 3);
v_nondep_2725_ = lean_ctor_get_uint8(v_e_2683_, sizeof(void*)*4 + 8);
v___x_2726_ = lean_ptr_addr(v_type_2722_);
v___x_2727_ = lean_ptr_addr(v_a_2714_);
v___x_2728_ = lean_usize_dec_eq(v___x_2726_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
lean_inc(v_declName_2721_);
lean_dec_ref_known(v_e_2683_, 4);
v___x_2729_ = l_Lean_Expr_letE___override(v_declName_2721_, v_a_2714_, v_a_2716_, v_b_2688_, v_nondep_2725_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2729_);
v___x_2731_ = v___x_2718_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
else
{
size_t v___x_2733_; size_t v___x_2734_; uint8_t v___x_2735_; 
v___x_2733_ = lean_ptr_addr(v_value_2723_);
v___x_2734_ = lean_ptr_addr(v_a_2716_);
v___x_2735_ = lean_usize_dec_eq(v___x_2733_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_inc(v_declName_2721_);
lean_dec_ref_known(v_e_2683_, 4);
v___x_2736_ = l_Lean_Expr_letE___override(v_declName_2721_, v_a_2714_, v_a_2716_, v_b_2688_, v_nondep_2725_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2736_);
v___x_2738_ = v___x_2718_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
else
{
size_t v___x_2740_; size_t v___x_2741_; uint8_t v___x_2742_; 
v___x_2740_ = lean_ptr_addr(v_body_2724_);
v___x_2741_ = lean_ptr_addr(v_b_2688_);
v___x_2742_ = lean_usize_dec_eq(v___x_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2745_; 
lean_inc(v_declName_2721_);
lean_dec_ref_known(v_e_2683_, 4);
v___x_2743_ = l_Lean_Expr_letE___override(v_declName_2721_, v_a_2714_, v_a_2716_, v_b_2688_, v_nondep_2725_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2743_);
v___x_2745_ = v___x_2718_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
else
{
lean_object* v___x_2748_; 
lean_dec(v_a_2716_);
lean_dec(v_a_2714_);
lean_dec_ref(v_b_2688_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_e_2683_);
v___x_2748_ = v___x_2718_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_e_2683_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
lean_dec(v_a_2716_);
lean_dec(v_a_2714_);
lean_dec_ref(v_b_2688_);
lean_dec_ref(v_e_2683_);
v___x_2750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2751_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2750_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2751_);
v___x_2753_ = v___x_2718_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
v___jp_2755_:
{
uint8_t v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = 0;
v___x_2766_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2761_, v_a_2714_, v_a_2716_, v___y_2760_, v___x_2712_, v___x_2765_, v___y_2756_, v___y_2763_, v___y_2757_, v___y_2758_, v___y_2762_, v___y_2759_, v___y_2764_);
return v___x_2766_;
}
v___jp_2772_:
{
if (v_underBinder_2768_ == 0)
{
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
goto v___jp_2720_;
}
else
{
if (v_descend_2767_ == 0)
{
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
goto v___jp_2720_;
}
else
{
lean_del_object(v___x_2718_);
lean_dec_ref(v_b_2688_);
lean_dec_ref(v_e_2683_);
v___y_2756_ = v___y_2773_;
v___y_2757_ = v___y_2774_;
v___y_2758_ = v___y_2775_;
v___y_2759_ = v___y_2776_;
v___y_2760_ = v___y_2778_;
v___y_2761_ = v___y_2777_;
v___y_2762_ = v___y_2779_;
v___y_2763_ = v___y_2780_;
v___y_2764_ = v___y_2781_;
goto v___jp_2755_;
}
}
}
v___jp_2782_:
{
lean_object* v___x_2791_; 
lean_inc(v_a_2716_);
lean_inc(v_a_2714_);
v___x_2791_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2682_, v_n_2685_, v_a_2714_, v_a_2716_, v___y_2784_, v___y_2786_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v_fst_2793_; lean_object* v_snd_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___f_2798_; uint8_t v___x_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v_fst_2793_ = lean_ctor_get(v_a_2792_, 0);
lean_inc_n(v_fst_2793_, 2);
v_snd_2794_ = lean_ctor_get(v_a_2792_, 1);
lean_inc(v_snd_2794_);
lean_dec(v_a_2792_);
v___x_2795_ = lean_box(v___x_2712_);
v___x_2796_ = lean_box(v_isLet_2684_);
v___x_2797_ = lean_box(v_topLevel_2689_);
lean_inc(v_a_2716_);
lean_inc(v_a_2714_);
lean_inc_ref(v_e_2683_);
lean_inc_ref(v_b_2688_);
v___f_2798_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2798_, 0, v_fst_2793_);
lean_closure_set(v___f_2798_, 1, v_fvars_2682_);
lean_closure_set(v___f_2798_, 2, v_b_2688_);
lean_closure_set(v___f_2798_, 3, v___x_2795_);
lean_closure_set(v___f_2798_, 4, v_e_2683_);
lean_closure_set(v___f_2798_, 5, v_a_2714_);
lean_closure_set(v___f_2798_, 6, v_a_2716_);
lean_closure_set(v___f_2798_, 7, v___x_2796_);
lean_closure_set(v___f_2798_, 8, v___x_2797_);
v___x_2799_ = lean_unbox(v_fst_2793_);
lean_dec(v_fst_2793_);
if (v___x_2799_ == 0)
{
v___y_2773_ = v___y_2784_;
v___y_2774_ = v___y_2786_;
v___y_2775_ = v___y_2787_;
v___y_2776_ = v___y_2789_;
v___y_2777_ = v_snd_2794_;
v___y_2778_ = v___f_2798_;
v___y_2779_ = v___y_2788_;
v___y_2780_ = v___y_2785_;
v___y_2781_ = v___y_2790_;
goto v___jp_2772_;
}
else
{
if (v___y_2783_ == 0)
{
lean_del_object(v___x_2718_);
lean_dec_ref(v_b_2688_);
lean_dec_ref(v_e_2683_);
v___y_2756_ = v___y_2784_;
v___y_2757_ = v___y_2786_;
v___y_2758_ = v___y_2787_;
v___y_2759_ = v___y_2789_;
v___y_2760_ = v___f_2798_;
v___y_2761_ = v_snd_2794_;
v___y_2762_ = v___y_2788_;
v___y_2763_ = v___y_2785_;
v___y_2764_ = v___y_2790_;
goto v___jp_2755_;
}
else
{
v___y_2773_ = v___y_2784_;
v___y_2774_ = v___y_2786_;
v___y_2775_ = v___y_2787_;
v___y_2776_ = v___y_2789_;
v___y_2777_ = v_snd_2794_;
v___y_2778_ = v___f_2798_;
v___y_2779_ = v___y_2788_;
v___y_2780_ = v___y_2785_;
v___y_2781_ = v___y_2790_;
goto v___jp_2772_;
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_del_object(v___x_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2714_);
lean_dec_ref(v_b_2688_);
lean_dec_ref(v_e_2683_);
lean_dec(v_fvars_2682_);
v_a_2800_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2791_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2791_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
v___jp_2808_:
{
if (v_merge_2770_ == 0)
{
v___y_2783_ = v___y_2809_;
v___y_2784_ = v_a_2690_;
v___y_2785_ = v_a_2691_;
v___y_2786_ = v_a_2692_;
v___y_2787_ = v_a_2693_;
v___y_2788_ = v_a_2694_;
v___y_2789_ = v_a_2695_;
v___y_2790_ = v_a_2696_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2810_; lean_object* v_valueMap_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_st_ref_get(v_a_2692_);
v_valueMap_2811_ = lean_ctor_get(v___x_2810_, 2);
lean_inc_ref(v_valueMap_2811_);
lean_dec(v___x_2810_);
v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2811_, v_a_2716_);
lean_dec_ref(v_valueMap_2811_);
if (lean_obj_tag(v___x_2812_) == 1)
{
lean_del_object(v___x_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2714_);
lean_dec(v_n_2685_);
lean_dec_ref(v_e_2683_);
if (v_isLet_2684_ == 0)
{
lean_object* v_val_2813_; 
v_val_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_val_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2699_ = v_val_2813_;
v___y_2700_ = v_a_2690_;
v___y_2701_ = v_a_2691_;
v___y_2702_ = v_a_2692_;
v___y_2703_ = v_a_2693_;
v___y_2704_ = v_a_2694_;
v___y_2705_ = v_a_2695_;
v___y_2706_ = v_a_2696_;
goto v___jp_2698_;
}
else
{
if (v_lift_2771_ == 0)
{
lean_object* v_val_2814_; 
v_val_2814_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_val_2814_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2699_ = v_val_2814_;
v___y_2700_ = v_a_2690_;
v___y_2701_ = v_a_2691_;
v___y_2702_ = v_a_2692_;
v___y_2703_ = v_a_2693_;
v___y_2704_ = v_a_2694_;
v___y_2705_ = v_a_2695_;
v___y_2706_ = v_a_2696_;
goto v___jp_2698_;
}
else
{
lean_object* v_val_2815_; lean_object* v___x_2816_; 
v_val_2815_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_val_2815_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2816_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2815_, v_a_2692_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_dec_ref_known(v___x_2816_, 1);
v___y_2699_ = v_val_2815_;
v___y_2700_ = v_a_2690_;
v___y_2701_ = v_a_2691_;
v___y_2702_ = v_a_2692_;
v___y_2703_ = v_a_2693_;
v___y_2704_ = v_a_2694_;
v___y_2705_ = v_a_2695_;
v___y_2706_ = v_a_2696_;
goto v___jp_2698_;
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v_val_2815_);
lean_dec_ref(v_b_2688_);
lean_dec(v_fvars_2682_);
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2816_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2812_);
v___y_2783_ = v___y_2809_;
v___y_2784_ = v_a_2690_;
v___y_2785_ = v_a_2691_;
v___y_2786_ = v_a_2692_;
v___y_2787_ = v_a_2693_;
v___y_2788_ = v_a_2694_;
v___y_2789_ = v_a_2695_;
v___y_2790_ = v_a_2696_;
goto v___jp_2782_;
}
}
}
}
}
else
{
lean_dec(v_a_2714_);
lean_dec_ref(v_b_2688_);
lean_dec(v_n_2685_);
lean_dec_ref(v_e_2683_);
lean_dec(v_fvars_2682_);
return v___x_2715_;
}
}
else
{
lean_dec_ref(v_b_2688_);
lean_dec_ref(v_v_2687_);
lean_dec(v_n_2685_);
lean_dec_ref(v_e_2683_);
lean_dec(v_fvars_2682_);
return v___x_2713_;
}
v___jp_2698_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_inc(v___y_2699_);
v___x_2707_ = l_Lean_Expr_fvar___override(v___y_2699_);
v___x_2708_ = lean_expr_instantiate1(v_b_2688_, v___x_2707_);
lean_dec_ref(v___x_2707_);
lean_dec_ref(v_b_2688_);
v___x_2709_ = lean_box(v_topLevel_2689_);
v___x_2710_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2710_, 0, v_fvars_2682_);
lean_closure_set(v___x_2710_, 1, v___x_2708_);
lean_closure_set(v___x_2710_, 2, v___x_2709_);
v___x_2711_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2699_, v___x_2710_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2699_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2828_, lean_object* v_struct_2829_, lean_object* v___y_2830_, lean_object* v_typeName_2831_, lean_object* v_idx_2832_, lean_object* v_e_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
uint8_t v___y_41873__boxed_2842_; lean_object* v_res_2843_; 
v___y_41873__boxed_2842_ = lean_unbox(v___y_2830_);
v_res_2843_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2828_, v_struct_2829_, v___y_41873__boxed_2842_, v_typeName_2831_, v_idx_2832_, v_e_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2843_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2847_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2848_ = lean_unsigned_to_nat(75u);
v___x_2849_ = lean_unsigned_to_nat(229u);
v___x_2850_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2851_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2852_ = l_mkPanicMessageWithDecl(v___x_2851_, v___x_2850_, v___x_2849_, v___x_2848_, v___x_2847_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2853_, lean_object* v_e_2854_, lean_object* v_fvars_2855_, uint8_t v___x_2856_, uint8_t v_topLevel_2857_, uint8_t v___y_2858_, lean_object* v_____r_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_k_2869_; 
switch(lean_obj_tag(v_e_2854_))
{
case 5:
{
lean_object* v___x_2872_; lean_object* v_dummy_2873_; lean_object* v_nargs_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2872_ = l_Lean_Expr_getAppFn(v_e_2854_);
v_dummy_2873_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2874_ = l_Lean_Expr_getAppNumArgs(v_e_2854_);
lean_inc(v_nargs_2874_);
v___x_2875_ = lean_mk_array(v_nargs_2874_, v_dummy_2873_);
v___x_2876_ = lean_unsigned_to_nat(1u);
v___x_2877_ = lean_nat_sub(v_nargs_2874_, v___x_2876_);
lean_dec(v_nargs_2874_);
lean_inc_ref(v_e_2854_);
v___x_2878_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2854_, v___x_2875_, v___x_2877_);
v___x_2879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2879_, 0, v_fvars_2855_);
lean_closure_set(v___x_2879_, 1, v___x_2872_);
lean_closure_set(v___x_2879_, 2, v___x_2878_);
v_k_2869_ = v___x_2879_;
goto v___jp_2868_;
}
case 6:
{
lean_object* v_binderName_2880_; lean_object* v_binderType_2881_; lean_object* v_body_2882_; uint8_t v_binderInfo_2883_; lean_object* v___x_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_binderName_2880_ = lean_ctor_get(v_e_2854_, 0);
v_binderType_2881_ = lean_ctor_get(v_e_2854_, 1);
v_body_2882_ = lean_ctor_get(v_e_2854_, 2);
v_binderInfo_2883_ = lean_ctor_get_uint8(v_e_2854_, sizeof(void*)*3 + 8);
v___x_2884_ = lean_box(v_binderInfo_2883_);
lean_inc_ref(v_e_2854_);
lean_inc_ref_n(v_body_2882_, 2);
lean_inc_n(v_binderName_2880_, 2);
lean_inc_ref_n(v_binderType_2881_, 2);
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2885_, 0, v_binderType_2881_);
lean_closure_set(v___f_2885_, 1, v_binderName_2880_);
lean_closure_set(v___f_2885_, 2, v___x_2884_);
lean_closure_set(v___f_2885_, 3, v_body_2882_);
lean_closure_set(v___f_2885_, 4, v_e_2854_);
v___x_2886_ = lean_box(v_binderInfo_2883_);
v___x_2887_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2887_, 0, v_fvars_2855_);
lean_closure_set(v___x_2887_, 1, v_binderName_2880_);
lean_closure_set(v___x_2887_, 2, v_binderType_2881_);
lean_closure_set(v___x_2887_, 3, v_body_2882_);
lean_closure_set(v___x_2887_, 4, v___x_2886_);
lean_closure_set(v___x_2887_, 5, v___f_2885_);
v_k_2869_ = v___x_2887_;
goto v___jp_2868_;
}
case 7:
{
lean_object* v_binderName_2888_; lean_object* v_binderType_2889_; lean_object* v_body_2890_; uint8_t v_binderInfo_2891_; lean_object* v___x_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_binderName_2888_ = lean_ctor_get(v_e_2854_, 0);
v_binderType_2889_ = lean_ctor_get(v_e_2854_, 1);
v_body_2890_ = lean_ctor_get(v_e_2854_, 2);
v_binderInfo_2891_ = lean_ctor_get_uint8(v_e_2854_, sizeof(void*)*3 + 8);
v___x_2892_ = lean_box(v_binderInfo_2891_);
lean_inc_ref(v_e_2854_);
lean_inc_ref_n(v_body_2890_, 2);
lean_inc_n(v_binderName_2888_, 2);
lean_inc_ref_n(v_binderType_2889_, 2);
v___f_2893_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2893_, 0, v_binderType_2889_);
lean_closure_set(v___f_2893_, 1, v_binderName_2888_);
lean_closure_set(v___f_2893_, 2, v___x_2892_);
lean_closure_set(v___f_2893_, 3, v_body_2890_);
lean_closure_set(v___f_2893_, 4, v_e_2854_);
v___x_2894_ = lean_box(v_binderInfo_2891_);
v___x_2895_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2895_, 0, v_fvars_2855_);
lean_closure_set(v___x_2895_, 1, v_binderName_2888_);
lean_closure_set(v___x_2895_, 2, v_binderType_2889_);
lean_closure_set(v___x_2895_, 3, v_body_2890_);
lean_closure_set(v___x_2895_, 4, v___x_2894_);
lean_closure_set(v___x_2895_, 5, v___f_2893_);
v_k_2869_ = v___x_2895_;
goto v___jp_2868_;
}
case 8:
{
uint8_t v_nondep_2896_; 
v_nondep_2896_ = lean_ctor_get_uint8(v_e_2854_, sizeof(void*)*4 + 8);
if (v_nondep_2896_ == 0)
{
lean_object* v_declName_2897_; lean_object* v_type_2898_; lean_object* v_value_2899_; lean_object* v_body_2900_; lean_object* v___x_2901_; 
v_declName_2897_ = lean_ctor_get(v_e_2854_, 0);
lean_inc(v_declName_2897_);
v_type_2898_ = lean_ctor_get(v_e_2854_, 1);
lean_inc_ref(v_type_2898_);
v_value_2899_ = lean_ctor_get(v_e_2854_, 2);
lean_inc_ref(v_value_2899_);
v_body_2900_ = lean_ctor_get(v_e_2854_, 3);
lean_inc_ref(v_body_2900_);
v___x_2901_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2855_, v_e_2854_, v___x_2856_, v_declName_2897_, v_type_2898_, v_value_2899_, v_body_2900_, v_topLevel_2857_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2901_;
}
else
{
lean_object* v_declName_2902_; lean_object* v_type_2903_; lean_object* v_value_2904_; lean_object* v_body_2905_; lean_object* v___x_2906_; 
v_declName_2902_ = lean_ctor_get(v_e_2854_, 0);
lean_inc(v_declName_2902_);
v_type_2903_ = lean_ctor_get(v_e_2854_, 1);
lean_inc_ref(v_type_2903_);
v_value_2904_ = lean_ctor_get(v_e_2854_, 2);
lean_inc_ref(v_value_2904_);
v_body_2905_ = lean_ctor_get(v_e_2854_, 3);
lean_inc_ref(v_body_2905_);
v___x_2906_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2855_, v_e_2854_, v___y_2858_, v_declName_2902_, v_type_2903_, v_value_2904_, v_body_2905_, v_topLevel_2857_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2906_;
}
}
case 10:
{
lean_object* v_data_2907_; lean_object* v_expr_2908_; lean_object* v___x_2909_; 
v_data_2907_ = lean_ctor_get(v_e_2854_, 0);
v_expr_2908_ = lean_ctor_get(v_e_2854_, 1);
lean_inc_ref(v_expr_2908_);
v___x_2909_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2855_, v_expr_2908_, v_topLevel_2857_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2924_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2924_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2924_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
size_t v___x_2914_; size_t v___x_2915_; uint8_t v___x_2916_; 
v___x_2914_ = lean_ptr_addr(v_expr_2908_);
v___x_2915_ = lean_ptr_addr(v_a_2910_);
v___x_2916_ = lean_usize_dec_eq(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2919_; 
lean_inc(v_data_2907_);
lean_dec_ref_known(v_e_2854_, 2);
v___x_2917_ = l_Lean_Expr_mdata___override(v_data_2907_, v_a_2910_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2917_);
v___x_2919_ = v___x_2912_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
else
{
lean_object* v___x_2922_; 
lean_dec(v_a_2910_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v_e_2854_);
v___x_2922_ = v___x_2912_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_e_2854_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2854_, 2);
return v___x_2909_;
}
}
case 11:
{
lean_object* v_typeName_2925_; lean_object* v_idx_2926_; lean_object* v_struct_2927_; lean_object* v___x_2928_; lean_object* v___f_2929_; 
v_typeName_2925_ = lean_ctor_get(v_e_2854_, 0);
v_idx_2926_ = lean_ctor_get(v_e_2854_, 1);
v_struct_2927_ = lean_ctor_get(v_e_2854_, 2);
v___x_2928_ = lean_box(v___y_2858_);
lean_inc_ref(v_e_2854_);
lean_inc(v_idx_2926_);
lean_inc(v_typeName_2925_);
lean_inc_ref(v_struct_2927_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2929_, 0, v_fvars_2855_);
lean_closure_set(v___f_2929_, 1, v_struct_2927_);
lean_closure_set(v___f_2929_, 2, v___x_2928_);
lean_closure_set(v___f_2929_, 3, v_typeName_2925_);
lean_closure_set(v___f_2929_, 4, v_idx_2926_);
lean_closure_set(v___f_2929_, 5, v_e_2854_);
v_k_2869_ = v___f_2929_;
goto v___jp_2868_;
}
default: 
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v_fvars_2855_);
lean_dec_ref(v_e_2854_);
v___x_2930_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2931_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2930_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2931_;
}
}
v___jp_2868_:
{
if (v_descend_2853_ == 0)
{
lean_object* v___x_2870_; 
lean_dec_ref(v_k_2869_);
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v_e_2854_);
return v___x_2870_;
}
else
{
lean_object* v___x_2871_; 
lean_dec_ref(v_e_2854_);
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
lean_inc(v___y_2864_);
lean_inc_ref(v___y_2863_);
lean_inc(v___y_2862_);
lean_inc(v___y_2861_);
lean_inc_ref(v___y_2860_);
v___x_2871_ = lean_apply_8(v_k_2869_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, lean_box(0));
return v___x_2871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2932_, lean_object* v_e_2933_, lean_object* v_fvars_2934_, lean_object* v___x_2935_, lean_object* v_topLevel_2936_, lean_object* v___y_2937_, lean_object* v_____r_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v_descend_boxed_2947_; uint8_t v___x_42026__boxed_2948_; uint8_t v_topLevel_boxed_2949_; uint8_t v___y_42027__boxed_2950_; lean_object* v_res_2951_; 
v_descend_boxed_2947_ = lean_unbox(v_descend_2932_);
v___x_42026__boxed_2948_ = lean_unbox(v___x_2935_);
v_topLevel_boxed_2949_ = lean_unbox(v_topLevel_2936_);
v___y_42027__boxed_2950_ = lean_unbox(v___y_2937_);
v_res_2951_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2947_, v_e_2933_, v_fvars_2934_, v___x_42026__boxed_2948_, v_topLevel_boxed_2949_, v___y_42027__boxed_2950_, v_____r_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_2952_, lean_object* v_e_2953_, uint8_t v_topLevel_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___y_2964_; lean_object* v_a_2965_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2975_; lean_object* v___y_2976_; uint8_t v___x_2979_; 
v___x_2979_ = l_Lean_Expr_isAtomic(v_e_2953_);
if (v___x_2979_ == 0)
{
uint8_t v_proofs_2980_; uint8_t v_types_2981_; uint8_t v_descend_2982_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; uint8_t v___y_2987_; uint8_t v___y_3004_; 
v_proofs_2980_ = lean_ctor_get_uint8(v_a_2955_, 0);
v_types_2981_ = lean_ctor_get_uint8(v_a_2955_, 1);
v_descend_2982_ = lean_ctor_get_uint8(v_a_2955_, 3);
if (v_descend_2982_ == 0)
{
goto v___jp_3028_;
}
else
{
if (v___x_2979_ == 0)
{
v___y_3004_ = v___x_2979_;
goto v___jp_3003_;
}
else
{
goto v___jp_3028_;
}
}
v___jp_2983_:
{
if (v___y_2987_ == 0)
{
lean_dec_ref(v___y_2985_);
if (v_proofs_2980_ == 0)
{
lean_object* v___x_2988_; 
lean_inc_ref(v_e_2953_);
v___x_2988_ = l_Lean_Meta_isProof(v_e_2953_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; uint8_t v___x_2990_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v___x_2990_ = lean_unbox(v_a_2989_);
lean_dec(v_a_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_dec_ref(v_e_2953_);
v___x_2991_ = lean_box(0);
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc(v_a_2956_);
lean_inc_ref(v_a_2955_);
v___x_2992_ = lean_apply_9(v___y_2986_, v___x_2991_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, lean_box(0));
v___y_2971_ = v___y_2984_;
v___y_2972_ = v___x_2992_;
goto v___jp_2970_;
}
else
{
lean_dec_ref(v___y_2986_);
v___y_2964_ = v___y_2984_;
v_a_2965_ = v_e_2953_;
goto v___jp_2963_;
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref(v___y_2986_);
lean_dec_ref(v___y_2984_);
lean_dec_ref(v_e_2953_);
v_a_2993_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2988_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2988_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_dec_ref(v_e_2953_);
v___x_3001_ = lean_box(0);
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc(v_a_2956_);
lean_inc_ref(v_a_2955_);
v___x_3002_ = lean_apply_9(v___y_2986_, v___x_3001_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, lean_box(0));
v___y_2971_ = v___y_2984_;
v___y_2972_ = v___x_3002_;
goto v___jp_2970_;
}
}
else
{
lean_dec_ref(v___y_2986_);
lean_dec_ref(v_e_2953_);
v___y_2975_ = v___y_2984_;
v___y_2976_ = v___y_2985_;
goto v___jp_2974_;
}
}
v___jp_3003_:
{
if (v___y_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = lean_st_ref_get(v_a_2956_);
v___x_3006_ = lean_box(v_topLevel_2954_);
lean_inc_ref(v_e_2953_);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
lean_ctor_set(v___x_3007_, 1, v_e_2953_);
v___x_3008_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3005_, v___x_3007_);
lean_dec(v___x_3005_);
if (lean_obj_tag(v___x_3008_) == 0)
{
uint8_t v___x_3009_; 
v___x_3009_ = l_Lean_Meta_ExtractLets_containsLet(v_e_2953_);
if (v___x_3009_ == 0)
{
lean_dec(v_fvars_2952_);
v___y_2964_ = v___x_3007_;
v_a_2965_ = v_e_2953_;
goto v___jp_2963_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v___f_3016_; 
v___x_3010_ = lean_box(v_descend_2982_);
v___x_3011_ = lean_box(v___x_3009_);
v___x_3012_ = lean_box(v_topLevel_2954_);
v___x_3013_ = lean_box(v___y_3004_);
lean_inc_ref_n(v_e_2953_, 2);
v___f_3014_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3014_, 0, v___x_3010_);
lean_closure_set(v___f_3014_, 1, v_e_2953_);
lean_closure_set(v___f_3014_, 2, v_fvars_2952_);
lean_closure_set(v___f_3014_, 3, v___x_3011_);
lean_closure_set(v___f_3014_, 4, v___x_3012_);
lean_closure_set(v___f_3014_, 5, v___x_3013_);
v___x_3015_ = lean_box(v_types_2981_);
lean_inc_ref(v___f_3014_);
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3016_, 0, v___x_3015_);
lean_closure_set(v___f_3016_, 1, v_e_2953_);
lean_closure_set(v___f_3016_, 2, v___f_3014_);
if (v_topLevel_2954_ == 0)
{
v___y_2984_ = v___x_3007_;
v___y_2985_ = v___f_3014_;
v___y_2986_ = v___f_3016_;
v___y_2987_ = v___x_2979_;
goto v___jp_2983_;
}
else
{
uint8_t v___x_3017_; 
v___x_3017_ = l_Lean_Expr_isLet(v_e_2953_);
if (v___x_3017_ == 0)
{
uint8_t v___x_3018_; 
v___x_3018_ = l_Lean_Expr_isMData(v_e_2953_);
v___y_2984_ = v___x_3007_;
v___y_2985_ = v___f_3014_;
v___y_2986_ = v___f_3016_;
v___y_2987_ = v___x_3018_;
goto v___jp_2983_;
}
else
{
lean_dec_ref(v___f_3016_);
lean_dec_ref(v_e_2953_);
v___y_2975_ = v___x_3007_;
v___y_2976_ = v___f_3014_;
goto v___jp_2974_;
}
}
}
}
else
{
lean_object* v_val_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref_known(v___x_3007_, 2);
lean_dec_ref(v_e_2953_);
lean_dec(v_fvars_2952_);
v_val_3019_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3008_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_val_3019_);
lean_dec(v___x_3008_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set_tag(v___x_3021_, 0);
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_val_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v___x_3027_; 
lean_dec(v_fvars_2952_);
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_e_2953_);
return v___x_3027_;
}
}
v___jp_3028_:
{
if (v_topLevel_2954_ == 0)
{
lean_object* v___x_3029_; 
lean_dec(v_fvars_2952_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_e_2953_);
return v___x_3029_;
}
else
{
v___y_3004_ = v___x_2979_;
goto v___jp_3003_;
}
}
}
else
{
lean_object* v___x_3030_; 
lean_dec(v_fvars_2952_);
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_e_2953_);
return v___x_3030_;
}
v___jp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2966_ = lean_st_ref_take(v_a_2956_);
lean_inc_ref(v_a_2965_);
v___x_2967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_2966_, v___y_2964_, v_a_2965_);
v___x_2968_ = lean_st_ref_put(v_a_2956_, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_a_2965_);
return v___x_2969_;
}
v___jp_2970_:
{
if (lean_obj_tag(v___y_2972_) == 0)
{
lean_object* v_a_2973_; 
v_a_2973_ = lean_ctor_get(v___y_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___y_2972_, 1);
v___y_2964_ = v___y_2971_;
v_a_2965_ = v_a_2973_;
goto v___jp_2963_;
}
else
{
lean_dec_ref(v___y_2971_);
return v___y_2972_;
}
}
v___jp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_box(0);
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc(v_a_2956_);
lean_inc_ref(v_a_2955_);
v___x_2978_ = lean_apply_9(v___y_2976_, v___x_2977_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, lean_box(0));
v___y_2971_ = v___y_2975_;
v___y_2972_ = v___x_2978_;
goto v___jp_2970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3031_, lean_object* v_struct_3032_, uint8_t v___y_3033_, lean_object* v_typeName_3034_, lean_object* v_idx_3035_, lean_object* v_e_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3045_; 
lean_inc_ref(v_struct_3032_);
v___x_3045_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3031_, v_struct_3032_, v___y_3033_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3060_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3060_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3060_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
size_t v___x_3050_; size_t v___x_3051_; uint8_t v___x_3052_; 
v___x_3050_ = lean_ptr_addr(v_struct_3032_);
lean_dec_ref(v_struct_3032_);
v___x_3051_ = lean_ptr_addr(v_a_3046_);
v___x_3052_ = lean_usize_dec_eq(v___x_3050_, v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
lean_dec_ref(v_e_3036_);
v___x_3053_ = l_Lean_Expr_proj___override(v_typeName_3034_, v_idx_3035_, v_a_3046_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v___x_3053_);
v___x_3055_ = v___x_3048_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
else
{
lean_object* v___x_3058_; 
lean_dec(v_a_3046_);
lean_dec(v_idx_3035_);
lean_dec(v_typeName_3034_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v_e_3036_);
v___x_3058_ = v___x_3048_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_e_3036_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_dec_ref(v_e_3036_);
lean_dec(v_idx_3035_);
lean_dec(v_typeName_3034_);
lean_dec_ref(v_struct_3032_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3061_, lean_object* v_sz_3062_, lean_object* v_i_3063_, lean_object* v_bs_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
size_t v_sz_boxed_3073_; size_t v_i_boxed_3074_; lean_object* v_res_3075_; 
v_sz_boxed_3073_ = lean_unbox_usize(v_sz_3062_);
lean_dec(v_sz_3062_);
v_i_boxed_3074_ = lean_unbox_usize(v_i_3063_);
lean_dec(v_i_3063_);
v_res_3075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3061_, v_sz_boxed_3073_, v_i_boxed_3074_, v_bs_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3076_, lean_object* v_fst_3077_, lean_object* v_fvars_3078_, lean_object* v_a_3079_, lean_object* v_b_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3076_, v_fst_3077_, v_fvars_3078_, v_a_3079_, v_b_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v_fst_3077_);
lean_dec(v_upperBound_3076_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3090_, lean_object* v_e_3091_, lean_object* v_isLet_3092_, lean_object* v_n_3093_, lean_object* v_t_3094_, lean_object* v_v_3095_, lean_object* v_b_3096_, lean_object* v_topLevel_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
uint8_t v_isLet_boxed_3106_; uint8_t v_topLevel_boxed_3107_; lean_object* v_res_3108_; 
v_isLet_boxed_3106_ = lean_unbox(v_isLet_3092_);
v_topLevel_boxed_3107_ = lean_unbox(v_topLevel_3097_);
v_res_3108_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3090_, v_e_3091_, v_isLet_boxed_3106_, v_n_3093_, v_t_3094_, v_v_3095_, v_b_3096_, v_topLevel_boxed_3107_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
lean_dec(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3109_, lean_object* v_name_3110_, lean_object* v_type_3111_, lean_object* v_val_3112_, lean_object* v_k_3113_, uint8_t v_nondep_3114_, uint8_t v_kind_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3110_, v_type_3111_, v_val_3112_, v_k_3113_, v_nondep_3114_, v_kind_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3125_, lean_object* v_name_3126_, lean_object* v_type_3127_, lean_object* v_val_3128_, lean_object* v_k_3129_, lean_object* v_nondep_3130_, lean_object* v_kind_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
uint8_t v_nondep_boxed_3140_; uint8_t v_kind_boxed_3141_; lean_object* v_res_3142_; 
v_nondep_boxed_3140_ = lean_unbox(v_nondep_3130_);
v_kind_boxed_3141_ = lean_unbox(v_kind_3131_);
v_res_3142_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3125_, v_name_3126_, v_type_3127_, v_val_3128_, v_k_3129_, v_nondep_boxed_3140_, v_kind_boxed_3141_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3143_, lean_object* v_m_3144_, lean_object* v_a_3145_, lean_object* v_b_3146_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3144_, v_a_3145_, v_b_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3148_, lean_object* v_m_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3149_, v_a_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3152_, lean_object* v_m_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3152_, v_m_3153_, v_a_3154_);
lean_dec_ref(v_a_3154_);
lean_dec_ref(v_m_3153_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3156_, lean_object* v_fst_3157_, lean_object* v_fvars_3158_, lean_object* v_inst_3159_, lean_object* v_R_3160_, lean_object* v_a_3161_, lean_object* v_b_3162_, lean_object* v_c_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3156_, v_fst_3157_, v_fvars_3158_, v_a_3161_, v_b_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3173_, lean_object* v_fst_3174_, lean_object* v_fvars_3175_, lean_object* v_inst_3176_, lean_object* v_R_3177_, lean_object* v_a_3178_, lean_object* v_b_3179_, lean_object* v_c_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3173_, v_fst_3174_, v_fvars_3175_, v_inst_3176_, v_R_3177_, v_a_3178_, v_b_3179_, v_c_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v_fst_3174_);
lean_dec(v_upperBound_3173_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3190_, lean_object* v_m_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3191_, v_a_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3194_, lean_object* v_m_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3194_, v_m_3195_, v_a_3196_);
lean_dec_ref(v_a_3196_);
lean_dec_ref(v_m_3195_);
return v_res_3197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3198_, lean_object* v_a_3199_, lean_object* v_x_3200_){
_start:
{
uint8_t v___x_3201_; 
v___x_3201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3199_, v_x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3202_, lean_object* v_a_3203_, lean_object* v_x_3204_){
_start:
{
uint8_t v_res_3205_; lean_object* v_r_3206_; 
v_res_3205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3202_, v_a_3203_, v_x_3204_);
lean_dec(v_x_3204_);
lean_dec_ref(v_a_3203_);
v_r_3206_ = lean_box(v_res_3205_);
return v_r_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3207_, lean_object* v_data_3208_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3210_, lean_object* v_a_3211_, lean_object* v_b_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3211_, v_b_3212_, v_x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3215_, lean_object* v_a_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3216_, v_x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3219_, lean_object* v_a_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3219_, v_a_3220_, v_x_3221_);
lean_dec(v_x_3221_);
lean_dec_ref(v_a_3220_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3223_, lean_object* v_a_3224_, lean_object* v_x_3225_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3224_, v_x_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3227_, lean_object* v_a_3228_, lean_object* v_x_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3227_, v_a_3228_, v_x_3229_);
lean_dec(v_x_3229_);
lean_dec_ref(v_a_3228_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3231_, lean_object* v_i_3232_, lean_object* v_source_3233_, lean_object* v_target_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3232_, v_source_3233_, v_target_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3236_, lean_object* v_x_3237_, lean_object* v_x_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3237_, v_x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v___x_3249_; lean_object* v_a_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; lean_object* v___x_3253_; 
v___x_3249_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3240_, v_a_3245_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = lean_box(0);
v___x_3252_ = 1;
v___x_3253_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3251_, v_a_3250_, v___x_3252_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3264_, size_t v_i_3265_, lean_object* v_bs_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_usize_dec_lt(v_i_3265_, v_sz_3264_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_bs_3266_);
return v___x_3276_;
}
else
{
lean_object* v_v_3277_; lean_object* v___x_3278_; 
v_v_3277_ = lean_array_uget_borrowed(v_bs_3266_, v_i_3265_);
lean_inc(v_v_3277_);
v___x_3278_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3277_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3280_; lean_object* v_bs_x27_3281_; size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = lean_unsigned_to_nat(0u);
v_bs_x27_3281_ = lean_array_uset(v_bs_3266_, v_i_3265_, v___x_3280_);
v___x_3282_ = ((size_t)1ULL);
v___x_3283_ = lean_usize_add(v_i_3265_, v___x_3282_);
v___x_3284_ = lean_array_uset(v_bs_x27_3281_, v_i_3265_, v_a_3279_);
v_i_3265_ = v___x_3283_;
v_bs_3266_ = v___x_3284_;
goto _start;
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec_ref(v_bs_3266_);
v_a_3286_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3278_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3278_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3294_, lean_object* v_i_3295_, lean_object* v_bs_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
size_t v_sz_boxed_3305_; size_t v_i_boxed_3306_; lean_object* v_res_3307_; 
v_sz_boxed_3305_ = lean_unbox_usize(v_sz_3294_);
lean_dec(v_sz_3294_);
v_i_boxed_3306_ = lean_unbox_usize(v_i_3295_);
lean_dec(v_i_3295_);
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3305_, v_i_boxed_3306_, v_bs_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v_merge_3328_; 
v_merge_3328_ = lean_ctor_get_uint8(v_a_3309_, 6);
if (v_merge_3328_ == 0)
{
v___y_3318_ = v_a_3309_;
v___y_3319_ = v_a_3310_;
v___y_3320_ = v_a_3311_;
v___y_3321_ = v_a_3312_;
v___y_3322_ = v_a_3313_;
v___y_3323_ = v_a_3314_;
v___y_3324_ = v_a_3315_;
goto v___jp_3317_;
}
else
{
uint8_t v_useContext_3329_; 
v_useContext_3329_ = lean_ctor_get_uint8(v_a_3309_, 7);
if (v_useContext_3329_ == 0)
{
v___y_3318_ = v_a_3309_;
v___y_3319_ = v_a_3310_;
v___y_3320_ = v_a_3311_;
v___y_3321_ = v_a_3312_;
v___y_3322_ = v_a_3313_;
v___y_3323_ = v_a_3314_;
v___y_3324_ = v_a_3315_;
goto v___jp_3317_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_dec_ref_known(v___x_3330_, 1);
v___y_3318_ = v_a_3309_;
v___y_3319_ = v_a_3310_;
v___y_3320_ = v_a_3311_;
v___y_3321_ = v_a_3312_;
v___y_3322_ = v_a_3313_;
v___y_3323_ = v_a_3314_;
v___y_3324_ = v_a_3315_;
goto v___jp_3317_;
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v_es_3308_);
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
v___jp_3317_:
{
size_t v_sz_3325_; size_t v___x_3326_; lean_object* v___x_3327_; 
v_sz_3325_ = lean_array_size(v_es_3308_);
v___x_3326_ = ((size_t)0ULL);
v___x_3327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3325_, v___x_3326_, v_es_3308_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Meta_ExtractLets_extract(v_es_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3349_, lean_object* v_x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3349_, v_x_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
v_a_3365_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3356_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3356_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3373_, v_x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3381_, lean_object* v_decls_3382_, lean_object* v_x_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3382_, v_x_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3390_, lean_object* v_decls_3391_, lean_object* v_x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3390_, v_decls_3391_, v_x_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3399_, size_t v_i_3400_, lean_object* v_bs_3401_){
_start:
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_usize_dec_lt(v_i_3400_, v_sz_3399_);
if (v___x_3402_ == 0)
{
return v_bs_3401_;
}
else
{
lean_object* v_v_3403_; lean_object* v___x_3404_; lean_object* v_bs_x27_3405_; lean_object* v___x_3406_; size_t v___x_3407_; size_t v___x_3408_; lean_object* v___x_3409_; 
v_v_3403_ = lean_array_uget(v_bs_3401_, v_i_3400_);
v___x_3404_ = lean_unsigned_to_nat(0u);
v_bs_x27_3405_ = lean_array_uset(v_bs_3401_, v_i_3400_, v___x_3404_);
v___x_3406_ = l_Lean_LocalDecl_fvarId(v_v_3403_);
lean_dec(v_v_3403_);
v___x_3407_ = ((size_t)1ULL);
v___x_3408_ = lean_usize_add(v_i_3400_, v___x_3407_);
v___x_3409_ = lean_array_uset(v_bs_x27_3405_, v_i_3400_, v___x_3406_);
v_i_3400_ = v___x_3408_;
v_bs_3401_ = v___x_3409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3411_, lean_object* v_i_3412_, lean_object* v_bs_3413_){
_start:
{
size_t v_sz_boxed_3414_; size_t v_i_boxed_3415_; lean_object* v_res_3416_; 
v_sz_boxed_3414_ = lean_unbox_usize(v_sz_3411_);
lean_dec(v_sz_3411_);
v_i_boxed_3415_ = lean_unbox_usize(v_i_3412_);
lean_dec(v_i_3412_);
v_res_3416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3414_, v_i_boxed_3415_, v_bs_3413_);
return v_res_3416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = lean_box(0);
v___x_3418_ = lean_unsigned_to_nat(16u);
v___x_3419_ = lean_mk_array(v___x_3418_, v___x_3417_);
return v___x_3419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___x_3420_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3423_, lean_object* v_givenNames_3424_, lean_object* v_k_3425_, lean_object* v_config_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3433_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3434_, 0, v_givenNames_3424_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
lean_ctor_set(v___x_3434_, 2, v___x_3432_);
v___x_3435_ = lean_st_mk_ref(v___x_3434_);
v___x_3436_ = lean_st_mk_ref(v___x_3432_);
v___x_3437_ = l_Lean_Meta_ExtractLets_extract(v_es_3423_, v_config_3426_, v___x_3436_, v___x_3435_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v_givenNames_3441_; lean_object* v_decls_3442_; size_t v_sz_3443_; size_t v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; size_t v_sz_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = lean_st_ref_get(v___x_3436_);
lean_dec(v___x_3436_);
lean_dec(v___x_3439_);
v___x_3440_ = lean_st_ref_get(v___x_3435_);
lean_dec(v___x_3435_);
v_givenNames_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_givenNames_3441_);
v_decls_3442_ = lean_ctor_get(v___x_3440_, 1);
lean_inc_ref(v_decls_3442_);
lean_dec(v___x_3440_);
v_sz_3443_ = lean_array_size(v_decls_3442_);
v___x_3444_ = ((size_t)0ULL);
v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_3443_, v___x_3444_, v_decls_3442_);
lean_inc_ref(v___x_3445_);
v___x_3446_ = lean_array_to_list(v___x_3445_);
v_sz_3447_ = lean_array_size(v___x_3445_);
v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3447_, v___x_3444_, v___x_3445_);
v___x_3449_ = lean_apply_3(v_k_3425_, v___x_3448_, v_a_3438_, v_givenNames_3441_);
v___x_3450_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3446_, v___x_3449_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3450_;
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v___x_3436_);
lean_dec(v___x_3435_);
lean_dec_ref(v_k_3425_);
v_a_3451_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3437_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3437_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3459_, lean_object* v_givenNames_3460_, lean_object* v_k_3461_, lean_object* v_config_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3459_, v_givenNames_3460_, v_k_3461_, v_config_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_config_3462_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3469_, lean_object* v_es_3470_, lean_object* v_givenNames_3471_, lean_object* v_k_3472_, lean_object* v_config_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3470_, v_givenNames_3471_, v_k_3472_, v_config_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3480_, lean_object* v_es_3481_, lean_object* v_givenNames_3482_, lean_object* v_k_3483_, lean_object* v_config_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3480_, v_es_3481_, v_givenNames_3482_, v_k_3483_, v_config_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_config_3484_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3491_, lean_object* v_runInBase_3492_, lean_object* v_b_3493_, lean_object* v_c_3494_, lean_object* v_d_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_apply_3(v_k_3491_, v_b_3493_, v_c_3494_, v_d_3495_);
lean_inc(v___y_3499_);
lean_inc_ref(v___y_3498_);
lean_inc(v___y_3497_);
lean_inc_ref(v___y_3496_);
v___x_3502_ = lean_apply_7(v_runInBase_3492_, lean_box(0), v___x_3501_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, lean_box(0));
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3503_, lean_object* v_runInBase_3504_, lean_object* v_b_3505_, lean_object* v_c_3506_, lean_object* v_d_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3503_, v_runInBase_3504_, v_b_3505_, v_c_3506_, v_d_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3514_, lean_object* v_es_3515_, lean_object* v_givenNames_3516_, lean_object* v_config_3517_, lean_object* v_runInBase_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___f_3524_; lean_object* v___x_3525_; 
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3524_, 0, v_k_3514_);
lean_closure_set(v___f_3524_, 1, v_runInBase_3518_);
v___x_3525_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3515_, v_givenNames_3516_, v___f_3524_, v_config_3517_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3526_, lean_object* v_es_3527_, lean_object* v_givenNames_3528_, lean_object* v_config_3529_, lean_object* v_runInBase_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3526_, v_es_3527_, v_givenNames_3528_, v_config_3529_, v_runInBase_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v_config_3529_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_es_3539_, lean_object* v_givenNames_3540_, lean_object* v_k_3541_, lean_object* v_config_3542_){
_start:
{
lean_object* v_toBind_3543_; lean_object* v_liftWith_3544_; lean_object* v_restoreM_3545_; lean_object* v___f_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v_toBind_3543_ = lean_ctor_get(v_inst_3537_, 1);
lean_inc(v_toBind_3543_);
lean_dec_ref(v_inst_3537_);
v_liftWith_3544_ = lean_ctor_get(v_inst_3538_, 0);
lean_inc(v_liftWith_3544_);
v_restoreM_3545_ = lean_ctor_get(v_inst_3538_, 1);
lean_inc(v_restoreM_3545_);
lean_dec_ref(v_inst_3538_);
v___f_3546_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3546_, 0, v_k_3541_);
lean_closure_set(v___f_3546_, 1, v_es_3539_);
lean_closure_set(v___f_3546_, 2, v_givenNames_3540_);
lean_closure_set(v___f_3546_, 3, v_config_3542_);
v___x_3547_ = lean_apply_2(v_liftWith_3544_, lean_box(0), v___f_3546_);
v___x_3548_ = lean_apply_1(v_restoreM_3545_, lean_box(0));
v___x_3549_ = lean_apply_4(v_toBind_3543_, lean_box(0), lean_box(0), v___x_3547_, v___x_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3550_, lean_object* v_00_u03b1_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_es_3554_, lean_object* v_givenNames_3555_, lean_object* v_k_3556_, lean_object* v_config_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_Meta_extractLets___redArg(v_inst_3552_, v_inst_3553_, v_es_3554_, v_givenNames_3555_, v_k_3556_, v_config_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3560_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3561_ = lean_box(0);
v___x_3562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
lean_ctor_set(v___x_3562_, 1, v___x_3560_);
lean_ctor_set(v___x_3562_, 2, v___x_3559_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3563_, lean_object* v_config_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v_proofs_3575_; uint8_t v_types_3576_; uint8_t v_implicits_3577_; uint8_t v_descend_3578_; uint8_t v_underBinder_3579_; uint8_t v_usedOnly_3580_; uint8_t v_merge_3581_; uint8_t v_useContext_3582_; uint8_t v_preserveBinderNames_3583_; uint8_t v_lift_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3618_; 
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3572_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3573_ = lean_st_mk_ref(v___x_3572_);
v___x_3574_ = lean_st_mk_ref(v___x_3571_);
v_proofs_3575_ = lean_ctor_get_uint8(v_config_3564_, 0);
v_types_3576_ = lean_ctor_get_uint8(v_config_3564_, 1);
v_implicits_3577_ = lean_ctor_get_uint8(v_config_3564_, 2);
v_descend_3578_ = lean_ctor_get_uint8(v_config_3564_, 3);
v_underBinder_3579_ = lean_ctor_get_uint8(v_config_3564_, 4);
v_usedOnly_3580_ = lean_ctor_get_uint8(v_config_3564_, 5);
v_merge_3581_ = lean_ctor_get_uint8(v_config_3564_, 6);
v_useContext_3582_ = lean_ctor_get_uint8(v_config_3564_, 7);
v_preserveBinderNames_3583_ = lean_ctor_get_uint8(v_config_3564_, 9);
v_lift_3584_ = lean_ctor_get_uint8(v_config_3564_, 10);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_config_3564_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3586_ = v_config_3564_;
v_isShared_3587_ = v_isSharedCheck_3618_;
goto v_resetjp_3585_;
}
else
{
lean_dec(v_config_3564_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3618_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; lean_object* v___x_3593_; 
v___x_3588_ = lean_unsigned_to_nat(1u);
v___x_3589_ = lean_mk_empty_array_with_capacity(v___x_3588_);
v___x_3590_ = lean_array_push(v___x_3589_, v_e_3563_);
v___x_3591_ = 1;
if (v_isShared_3587_ == 0)
{
v___x_3593_ = v___x_3586_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 0, v_proofs_3575_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 1, v_types_3576_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 2, v_implicits_3577_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 3, v_descend_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 4, v_underBinder_3579_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 5, v_usedOnly_3580_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 6, v_merge_3581_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 7, v_useContext_3582_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 9, v_preserveBinderNames_3583_);
lean_ctor_set_uint8(v_reuseFailAlloc_3617_, 10, v_lift_3584_);
v___x_3593_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; 
lean_ctor_set_uint8(v___x_3593_, 8, v___x_3591_);
v___x_3594_ = l_Lean_Meta_ExtractLets_extract(v___x_3590_, v___x_3593_, v___x_3574_, v___x_3573_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
lean_dec_ref(v___x_3593_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3608_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3608_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3608_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v_decls_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3599_ = lean_st_ref_get(v___x_3574_);
lean_dec(v___x_3574_);
lean_dec(v___x_3599_);
v___x_3600_ = lean_st_ref_get(v___x_3573_);
lean_dec(v___x_3573_);
v_decls_3601_ = lean_ctor_get(v___x_3600_, 1);
lean_inc_ref(v_decls_3601_);
lean_dec(v___x_3600_);
v___x_3602_ = l_Lean_instInhabitedExpr;
v___x_3603_ = lean_array_get(v___x_3602_, v_a_3595_, v___x_3570_);
lean_dec(v_a_3595_);
v___x_3604_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3601_, v___x_3603_);
lean_dec_ref(v_decls_3601_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3604_);
v___x_3606_ = v___x_3597_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v___x_3574_);
lean_dec(v___x_3573_);
v_a_3609_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3594_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3594_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3619_, lean_object* v_config_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_Meta_liftLets(v_e_3619_, v_config_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
return v_res_3626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3629_ = l_Lean_stringToMessageData(v___x_3628_);
return v___x_3629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3632_, lean_object* v_mvarId_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3640_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3632_, v_mvarId_3633_, v___x_3639_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3641_, lean_object* v_mvarId_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3641_, v_mvarId_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3649_, lean_object* v_tactic_3650_, lean_object* v_mvarId_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3650_, v_mvarId_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3658_, lean_object* v_tactic_3659_, lean_object* v_mvarId_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3658_, v_tactic_3659_, v_mvarId_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
lean_dec(v_a_3664_);
lean_dec_ref(v_a_3663_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3667_, lean_object* v_b_3668_, lean_object* v_c_3669_, lean_object* v_d_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; 
lean_inc(v___y_3674_);
lean_inc_ref(v___y_3673_);
lean_inc(v___y_3672_);
lean_inc_ref(v___y_3671_);
v___x_3676_ = lean_apply_8(v_k_3667_, v_b_3668_, v_c_3669_, v_d_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, lean_box(0));
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3677_, lean_object* v_b_3678_, lean_object* v_c_3679_, lean_object* v_d_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3677_, v_b_3678_, v_c_3679_, v_d_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3687_, lean_object* v_givenNames_3688_, lean_object* v_k_3689_, lean_object* v_config_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v___f_3696_; lean_object* v___x_3697_; 
v___f_3696_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3696_, 0, v_k_3689_);
v___x_3697_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3687_, v_givenNames_3688_, v___f_3696_, v_config_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3697_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
v_a_3706_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3697_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3697_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3714_, lean_object* v_givenNames_3715_, lean_object* v_k_3716_, lean_object* v_config_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3714_, v_givenNames_3715_, v_k_3716_, v_config_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_config_3717_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3724_, lean_object* v_es_3725_, lean_object* v_givenNames_3726_, lean_object* v_k_3727_, lean_object* v_config_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3725_, v_givenNames_3726_, v_k_3727_, v_config_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3735_, lean_object* v_es_3736_, lean_object* v_givenNames_3737_, lean_object* v_k_3738_, lean_object* v_config_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3735_, v_es_3736_, v_givenNames_3737_, v_k_3738_, v_config_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec_ref(v_config_3739_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3746_, v_x_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3753_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3753_);
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
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
v_a_3762_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3753_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3753_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3770_, lean_object* v_x_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3770_, v_x_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3778_, lean_object* v_mvarId_3779_, lean_object* v_x_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3779_, v_x_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3787_, lean_object* v_mvarId_3788_, lean_object* v_x_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3787_, v_mvarId_3788_, v_x_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3796_, lean_object* v_x_3797_, lean_object* v_x_3798_, lean_object* v_x_3799_){
_start:
{
lean_object* v_ks_3800_; lean_object* v_vs_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3825_; 
v_ks_3800_ = lean_ctor_get(v_x_3796_, 0);
v_vs_3801_ = lean_ctor_get(v_x_3796_, 1);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_x_3796_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3803_ = v_x_3796_;
v_isShared_3804_ = v_isSharedCheck_3825_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_vs_3801_);
lean_inc(v_ks_3800_);
lean_dec(v_x_3796_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3825_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; uint8_t v___x_3806_; 
v___x_3805_ = lean_array_get_size(v_ks_3800_);
v___x_3806_ = lean_nat_dec_lt(v_x_3797_, v___x_3805_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
lean_dec(v_x_3797_);
v___x_3807_ = lean_array_push(v_ks_3800_, v_x_3798_);
v___x_3808_ = lean_array_push(v_vs_3801_, v_x_3799_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 1, v___x_3808_);
lean_ctor_set(v___x_3803_, 0, v___x_3807_);
v___x_3810_ = v___x_3803_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
else
{
lean_object* v_k_x27_3812_; uint8_t v___x_3813_; 
v_k_x27_3812_ = lean_array_fget_borrowed(v_ks_3800_, v_x_3797_);
v___x_3813_ = l_Lean_instBEqMVarId_beq(v_x_3798_, v_k_x27_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3815_; 
if (v_isShared_3804_ == 0)
{
v___x_3815_ = v___x_3803_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_ks_3800_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_vs_3801_);
v___x_3815_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = lean_unsigned_to_nat(1u);
v___x_3817_ = lean_nat_add(v_x_3797_, v___x_3816_);
lean_dec(v_x_3797_);
v_x_3796_ = v___x_3815_;
v_x_3797_ = v___x_3817_;
goto _start;
}
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3820_ = lean_array_fset(v_ks_3800_, v_x_3797_, v_x_3798_);
v___x_3821_ = lean_array_fset(v_vs_3801_, v_x_3797_, v_x_3799_);
lean_dec(v_x_3797_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 1, v___x_3821_);
lean_ctor_set(v___x_3803_, 0, v___x_3820_);
v___x_3823_ = v___x_3803_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3826_, lean_object* v_k_3827_, lean_object* v_v_3828_){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = lean_unsigned_to_nat(0u);
v___x_3830_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3826_, v___x_3829_, v_k_3827_, v_v_3828_);
return v___x_3830_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3832_, size_t v_x_3833_, size_t v_x_3834_, lean_object* v_x_3835_, lean_object* v_x_3836_){
_start:
{
if (lean_obj_tag(v_x_3832_) == 0)
{
lean_object* v_es_3837_; size_t v___x_3838_; size_t v___x_3839_; lean_object* v_j_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_es_3837_ = lean_ctor_get(v_x_3832_, 0);
v___x_3838_ = ((size_t)31ULL);
v___x_3839_ = lean_usize_land(v_x_3833_, v___x_3838_);
v_j_3840_ = lean_usize_to_nat(v___x_3839_);
v___x_3841_ = lean_array_get_size(v_es_3837_);
v___x_3842_ = lean_nat_dec_lt(v_j_3840_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_dec(v_j_3840_);
lean_dec(v_x_3836_);
lean_dec(v_x_3835_);
return v_x_3832_;
}
else
{
lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3881_; 
lean_inc_ref(v_es_3837_);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_x_3832_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v_x_3832_, 0);
lean_dec(v_unused_3882_);
v___x_3844_ = v_x_3832_;
v_isShared_3845_ = v_isSharedCheck_3881_;
goto v_resetjp_3843_;
}
else
{
lean_dec(v_x_3832_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3881_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v_v_3846_; lean_object* v___x_3847_; lean_object* v_xs_x27_3848_; lean_object* v___y_3850_; 
v_v_3846_ = lean_array_fget(v_es_3837_, v_j_3840_);
v___x_3847_ = lean_box(0);
v_xs_x27_3848_ = lean_array_fset(v_es_3837_, v_j_3840_, v___x_3847_);
switch(lean_obj_tag(v_v_3846_))
{
case 0:
{
lean_object* v_key_3855_; lean_object* v_val_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3866_; 
v_key_3855_ = lean_ctor_get(v_v_3846_, 0);
v_val_3856_ = lean_ctor_get(v_v_3846_, 1);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_v_3846_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3858_ = v_v_3846_;
v_isShared_3859_ = v_isSharedCheck_3866_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_val_3856_);
lean_inc(v_key_3855_);
lean_dec(v_v_3846_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3866_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
uint8_t v___x_3860_; 
v___x_3860_ = l_Lean_instBEqMVarId_beq(v_x_3835_, v_key_3855_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_del_object(v___x_3858_);
v___x_3861_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3855_, v_val_3856_, v_x_3835_, v_x_3836_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
v___y_3850_ = v___x_3862_;
goto v___jp_3849_;
}
else
{
lean_object* v___x_3864_; 
lean_dec(v_val_3856_);
lean_dec(v_key_3855_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 1, v_x_3836_);
lean_ctor_set(v___x_3858_, 0, v_x_3835_);
v___x_3864_ = v___x_3858_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_x_3835_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_x_3836_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
v___y_3850_ = v___x_3864_;
goto v___jp_3849_;
}
}
}
}
case 1:
{
lean_object* v_node_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3879_; 
v_node_3867_ = lean_ctor_get(v_v_3846_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_v_3846_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3869_ = v_v_3846_;
v_isShared_3870_ = v_isSharedCheck_3879_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_node_3867_);
lean_dec(v_v_3846_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3879_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
size_t v___x_3871_; size_t v___x_3872_; size_t v___x_3873_; size_t v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v___x_3871_ = ((size_t)5ULL);
v___x_3872_ = lean_usize_shift_right(v_x_3833_, v___x_3871_);
v___x_3873_ = ((size_t)1ULL);
v___x_3874_ = lean_usize_add(v_x_3834_, v___x_3873_);
v___x_3875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3867_, v___x_3872_, v___x_3874_, v_x_3835_, v_x_3836_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3875_);
v___x_3877_ = v___x_3869_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
v___y_3850_ = v___x_3877_;
goto v___jp_3849_;
}
}
}
default: 
{
lean_object* v___x_3880_; 
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_x_3835_);
lean_ctor_set(v___x_3880_, 1, v_x_3836_);
v___y_3850_ = v___x_3880_;
goto v___jp_3849_;
}
}
v___jp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
v___x_3851_ = lean_array_fset(v_xs_x27_3848_, v_j_3840_, v___y_3850_);
lean_dec(v_j_3840_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v___x_3851_);
v___x_3853_ = v___x_3844_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
else
{
lean_object* v_ks_3883_; lean_object* v_vs_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3902_; 
v_ks_3883_ = lean_ctor_get(v_x_3832_, 0);
v_vs_3884_ = lean_ctor_get(v_x_3832_, 1);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_x_3832_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3886_ = v_x_3832_;
v_isShared_3887_ = v_isSharedCheck_3902_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_vs_3884_);
lean_inc(v_ks_3883_);
lean_dec(v_x_3832_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3902_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_ks_3883_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_vs_3884_);
v___x_3889_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v_newNode_3890_; size_t v___x_3891_; uint8_t v___x_3892_; 
v_newNode_3890_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3889_, v_x_3835_, v_x_3836_);
v___x_3891_ = ((size_t)7ULL);
v___x_3892_ = lean_usize_dec_le(v___x_3891_, v_x_3834_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3893_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3890_);
v___x_3894_ = lean_unsigned_to_nat(4u);
v___x_3895_ = lean_nat_dec_lt(v___x_3893_, v___x_3894_);
lean_dec(v___x_3893_);
if (v___x_3895_ == 0)
{
lean_object* v_ks_3896_; lean_object* v_vs_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_ks_3896_ = lean_ctor_get(v_newNode_3890_, 0);
lean_inc_ref(v_ks_3896_);
v_vs_3897_ = lean_ctor_get(v_newNode_3890_, 1);
lean_inc_ref(v_vs_3897_);
lean_dec_ref(v_newNode_3890_);
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3834_, v_ks_3896_, v_vs_3897_, v___x_3898_, v___x_3899_);
lean_dec_ref(v_vs_3897_);
lean_dec_ref(v_ks_3896_);
return v___x_3900_;
}
else
{
return v_newNode_3890_;
}
}
else
{
return v_newNode_3890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3903_, lean_object* v_keys_3904_, lean_object* v_vals_3905_, lean_object* v_i_3906_, lean_object* v_entries_3907_){
_start:
{
lean_object* v___x_3908_; uint8_t v___x_3909_; 
v___x_3908_ = lean_array_get_size(v_keys_3904_);
v___x_3909_ = lean_nat_dec_lt(v_i_3906_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_dec(v_i_3906_);
return v_entries_3907_;
}
else
{
lean_object* v_k_3910_; lean_object* v_v_3911_; uint64_t v___x_3912_; size_t v_h_3913_; size_t v___x_3914_; lean_object* v___x_3915_; size_t v___x_3916_; size_t v___x_3917_; size_t v___x_3918_; size_t v_h_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_k_3910_ = lean_array_fget_borrowed(v_keys_3904_, v_i_3906_);
v_v_3911_ = lean_array_fget_borrowed(v_vals_3905_, v_i_3906_);
v___x_3912_ = l_Lean_instHashableMVarId_hash(v_k_3910_);
v_h_3913_ = lean_uint64_to_usize(v___x_3912_);
v___x_3914_ = ((size_t)5ULL);
v___x_3915_ = lean_unsigned_to_nat(1u);
v___x_3916_ = ((size_t)1ULL);
v___x_3917_ = lean_usize_sub(v_depth_3903_, v___x_3916_);
v___x_3918_ = lean_usize_mul(v___x_3914_, v___x_3917_);
v_h_3919_ = lean_usize_shift_right(v_h_3913_, v___x_3918_);
v___x_3920_ = lean_nat_add(v_i_3906_, v___x_3915_);
lean_dec(v_i_3906_);
lean_inc(v_v_3911_);
lean_inc(v_k_3910_);
v___x_3921_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3907_, v_h_3919_, v_depth_3903_, v_k_3910_, v_v_3911_);
v_i_3906_ = v___x_3920_;
v_entries_3907_ = v___x_3921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3923_, lean_object* v_keys_3924_, lean_object* v_vals_3925_, lean_object* v_i_3926_, lean_object* v_entries_3927_){
_start:
{
size_t v_depth_boxed_3928_; lean_object* v_res_3929_; 
v_depth_boxed_3928_ = lean_unbox_usize(v_depth_3923_);
lean_dec(v_depth_3923_);
v_res_3929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3928_, v_keys_3924_, v_vals_3925_, v_i_3926_, v_entries_3927_);
lean_dec_ref(v_vals_3925_);
lean_dec_ref(v_keys_3924_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3930_, lean_object* v_x_3931_, lean_object* v_x_3932_, lean_object* v_x_3933_, lean_object* v_x_3934_){
_start:
{
size_t v_x_2293__boxed_3935_; size_t v_x_2294__boxed_3936_; lean_object* v_res_3937_; 
v_x_2293__boxed_3935_ = lean_unbox_usize(v_x_3931_);
lean_dec(v_x_3931_);
v_x_2294__boxed_3936_ = lean_unbox_usize(v_x_3932_);
lean_dec(v_x_3932_);
v_res_3937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3930_, v_x_2293__boxed_3935_, v_x_2294__boxed_3936_, v_x_3933_, v_x_3934_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3938_, lean_object* v_x_3939_, lean_object* v_x_3940_){
_start:
{
uint64_t v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; lean_object* v___x_3944_; 
v___x_3941_ = l_Lean_instHashableMVarId_hash(v_x_3939_);
v___x_3942_ = lean_uint64_to_usize(v___x_3941_);
v___x_3943_ = ((size_t)1ULL);
v___x_3944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3938_, v___x_3942_, v___x_3943_, v_x_3939_, v_x_3940_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_3945_, lean_object* v_val_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; lean_object* v_mctx_3950_; lean_object* v_cache_3951_; lean_object* v_zetaDeltaFVarIds_3952_; lean_object* v_postponed_3953_; lean_object* v_diag_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3983_; 
v___x_3949_ = lean_st_ref_take(v___y_3947_);
v_mctx_3950_ = lean_ctor_get(v___x_3949_, 0);
v_cache_3951_ = lean_ctor_get(v___x_3949_, 1);
v_zetaDeltaFVarIds_3952_ = lean_ctor_get(v___x_3949_, 2);
v_postponed_3953_ = lean_ctor_get(v___x_3949_, 3);
v_diag_3954_ = lean_ctor_get(v___x_3949_, 4);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3956_ = v___x_3949_;
v_isShared_3957_ = v_isSharedCheck_3983_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_diag_3954_);
lean_inc(v_postponed_3953_);
lean_inc(v_zetaDeltaFVarIds_3952_);
lean_inc(v_cache_3951_);
lean_inc(v_mctx_3950_);
lean_dec(v___x_3949_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3983_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v_depth_3958_; lean_object* v_levelAssignDepth_3959_; lean_object* v_lmvarCounter_3960_; lean_object* v_mvarCounter_3961_; lean_object* v_lDecls_3962_; lean_object* v_decls_3963_; lean_object* v_userNames_3964_; lean_object* v_lAssignment_3965_; lean_object* v_eAssignment_3966_; lean_object* v_dAssignment_3967_; lean_object* v_instanceTypedMVars_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3982_; 
v_depth_3958_ = lean_ctor_get(v_mctx_3950_, 0);
v_levelAssignDepth_3959_ = lean_ctor_get(v_mctx_3950_, 1);
v_lmvarCounter_3960_ = lean_ctor_get(v_mctx_3950_, 2);
v_mvarCounter_3961_ = lean_ctor_get(v_mctx_3950_, 3);
v_lDecls_3962_ = lean_ctor_get(v_mctx_3950_, 4);
v_decls_3963_ = lean_ctor_get(v_mctx_3950_, 5);
v_userNames_3964_ = lean_ctor_get(v_mctx_3950_, 6);
v_lAssignment_3965_ = lean_ctor_get(v_mctx_3950_, 7);
v_eAssignment_3966_ = lean_ctor_get(v_mctx_3950_, 8);
v_dAssignment_3967_ = lean_ctor_get(v_mctx_3950_, 9);
v_instanceTypedMVars_3968_ = lean_ctor_get(v_mctx_3950_, 10);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_mctx_3950_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3970_ = v_mctx_3950_;
v_isShared_3971_ = v_isSharedCheck_3982_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_instanceTypedMVars_3968_);
lean_inc(v_dAssignment_3967_);
lean_inc(v_eAssignment_3966_);
lean_inc(v_lAssignment_3965_);
lean_inc(v_userNames_3964_);
lean_inc(v_decls_3963_);
lean_inc(v_lDecls_3962_);
lean_inc(v_mvarCounter_3961_);
lean_inc(v_lmvarCounter_3960_);
lean_inc(v_levelAssignDepth_3959_);
lean_inc(v_depth_3958_);
lean_dec(v_mctx_3950_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3982_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3972_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_3966_, v_mvarId_3945_, v_val_3946_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 8, v___x_3972_);
v___x_3974_ = v___x_3970_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_depth_3958_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_levelAssignDepth_3959_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_lmvarCounter_3960_);
lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_mvarCounter_3961_);
lean_ctor_set(v_reuseFailAlloc_3981_, 4, v_lDecls_3962_);
lean_ctor_set(v_reuseFailAlloc_3981_, 5, v_decls_3963_);
lean_ctor_set(v_reuseFailAlloc_3981_, 6, v_userNames_3964_);
lean_ctor_set(v_reuseFailAlloc_3981_, 7, v_lAssignment_3965_);
lean_ctor_set(v_reuseFailAlloc_3981_, 8, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3981_, 9, v_dAssignment_3967_);
lean_ctor_set(v_reuseFailAlloc_3981_, 10, v_instanceTypedMVars_3968_);
v___x_3974_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3976_; 
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3974_);
v___x_3976_ = v___x_3956_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_cache_3951_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_zetaDeltaFVarIds_3952_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_postponed_3953_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v_diag_3954_);
v___x_3976_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = lean_st_ref_put(v___y_3947_, v___x_3976_);
v___x_3978_ = lean_box(0);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_3984_, lean_object* v_val_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_3984_, v_val_3985_, v___y_3986_);
lean_dec(v___y_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_3989_, size_t v_i_3990_, lean_object* v_bs_3991_){
_start:
{
uint8_t v___x_3992_; 
v___x_3992_ = lean_usize_dec_lt(v_i_3990_, v_sz_3989_);
if (v___x_3992_ == 0)
{
return v_bs_3991_;
}
else
{
lean_object* v_v_3993_; lean_object* v___x_3994_; lean_object* v_bs_x27_3995_; lean_object* v___x_3996_; size_t v___x_3997_; size_t v___x_3998_; lean_object* v___x_3999_; 
v_v_3993_ = lean_array_uget(v_bs_3991_, v_i_3990_);
v___x_3994_ = lean_unsigned_to_nat(0u);
v_bs_x27_3995_ = lean_array_uset(v_bs_3991_, v_i_3990_, v___x_3994_);
v___x_3996_ = l_Lean_Expr_fvar___override(v_v_3993_);
v___x_3997_ = ((size_t)1ULL);
v___x_3998_ = lean_usize_add(v_i_3990_, v___x_3997_);
v___x_3999_ = lean_array_uset(v_bs_x27_3995_, v_i_3990_, v___x_3996_);
v_i_3990_ = v___x_3998_;
v_bs_3991_ = v___x_3999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4001_, lean_object* v_i_4002_, lean_object* v_bs_4003_){
_start:
{
size_t v_sz_boxed_4004_; size_t v_i_boxed_4005_; lean_object* v_res_4006_; 
v_sz_boxed_4004_ = lean_unbox_usize(v_sz_4001_);
lean_dec(v_sz_4001_);
v_i_boxed_4005_ = lean_unbox_usize(v_i_4002_);
lean_dec(v_i_4002_);
v_res_4006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4004_, v_i_boxed_4005_, v_bs_4003_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4007_, lean_object* v_mvarId_4008_, lean_object* v_a_4009_, lean_object* v___x_4010_, lean_object* v_fvarIds_4011_, lean_object* v_es_4012_, lean_object* v_givenNames_x27_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4070_; uint8_t v___x_4071_; 
v___x_4019_ = lean_unsigned_to_nat(0u);
v___x_4020_ = lean_array_get_borrowed(v___x_4007_, v_es_4012_, v___x_4019_);
v___x_4070_ = lean_array_get_size(v_fvarIds_4011_);
v___x_4071_ = lean_nat_dec_eq(v___x_4070_, v___x_4019_);
if (v___x_4071_ == 0)
{
lean_dec(v___x_4010_);
goto v___jp_4021_;
}
else
{
uint8_t v___x_4072_; 
v___x_4072_ = lean_expr_eqv(v_a_4009_, v___x_4020_);
if (v___x_4072_ == 0)
{
lean_dec(v___x_4010_);
goto v___jp_4021_;
}
else
{
lean_object* v___x_4073_; 
lean_inc(v_mvarId_4008_);
v___x_4073_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4010_, v_mvarId_4008_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_dec_ref_known(v___x_4073_, 1);
goto v___jp_4021_;
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v_givenNames_x27_4013_);
lean_dec_ref(v_fvarIds_4011_);
lean_dec(v_mvarId_4008_);
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
v___jp_4021_:
{
lean_object* v___x_4022_; 
lean_inc(v_mvarId_4008_);
v___x_4022_ = l_Lean_MVarId_getTag(v_mvarId_4008_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4024_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4022_, 1);
lean_inc(v___x_4020_);
v___x_4024_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4020_, v_a_4023_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; size_t v_sz_4026_; size_t v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; uint8_t v___x_4030_; uint8_t v___x_4031_; lean_object* v___x_4032_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc_n(v_a_4025_, 2);
lean_dec_ref_known(v___x_4024_, 1);
v_sz_4026_ = lean_array_size(v_fvarIds_4011_);
v___x_4027_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4011_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4026_, v___x_4027_, v_fvarIds_4011_);
v___x_4029_ = 0;
v___x_4030_ = 1;
v___x_4031_ = 1;
v___x_4032_ = l_Lean_Meta_mkLetFVars(v___x_4028_, v_a_4025_, v___x_4029_, v___x_4030_, v___x_4031_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec_ref(v___x_4028_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4044_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v___x_4034_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4008_, v_a_4033_, v___y_4015_);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; 
v_unused_4045_ = lean_ctor_get(v___x_4034_, 0);
lean_dec(v_unused_4045_);
v___x_4036_ = v___x_4034_;
v_isShared_4037_ = v_isSharedCheck_4044_;
goto v_resetjp_4035_;
}
else
{
lean_dec(v___x_4034_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4044_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4042_; 
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v_fvarIds_4011_);
lean_ctor_set(v___x_4038_, 1, v_givenNames_x27_4013_);
v___x_4039_ = l_Lean_Expr_mvarId_x21(v_a_4025_);
lean_dec(v_a_4025_);
v___x_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4038_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v___x_4040_);
v___x_4042_ = v___x_4036_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_a_4025_);
lean_dec(v_givenNames_x27_4013_);
lean_dec_ref(v_fvarIds_4011_);
lean_dec(v_mvarId_4008_);
v_a_4046_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4032_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4032_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec(v_givenNames_x27_4013_);
lean_dec_ref(v_fvarIds_4011_);
lean_dec(v_mvarId_4008_);
v_a_4054_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4024_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4024_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v_givenNames_x27_4013_);
lean_dec_ref(v_fvarIds_4011_);
lean_dec(v_mvarId_4008_);
v_a_4062_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4022_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4022_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4082_, lean_object* v_mvarId_4083_, lean_object* v_a_4084_, lean_object* v___x_4085_, lean_object* v_fvarIds_4086_, lean_object* v_es_4087_, lean_object* v_givenNames_x27_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_MVarId_extractLets___lam__0(v___x_4082_, v_mvarId_4083_, v_a_4084_, v___x_4085_, v_fvarIds_4086_, v_es_4087_, v_givenNames_x27_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec_ref(v_es_4087_);
lean_dec_ref(v_a_4084_);
lean_dec_ref(v___x_4082_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4095_, lean_object* v___x_4096_, lean_object* v___x_4097_, lean_object* v_givenNames_4098_, lean_object* v_config_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___x_4105_; 
lean_inc(v___x_4096_);
lean_inc(v_mvarId_4095_);
v___x_4105_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4095_, v___x_4096_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v___x_4106_; 
lean_dec_ref_known(v___x_4105_, 1);
lean_inc(v_mvarId_4095_);
v___x_4106_ = l_Lean_MVarId_getType(v_mvarId_4095_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___f_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc_n(v_a_4107_, 2);
lean_dec_ref_known(v___x_4106_, 1);
v___f_4108_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4108_, 0, v___x_4097_);
lean_closure_set(v___f_4108_, 1, v_mvarId_4095_);
lean_closure_set(v___f_4108_, 2, v_a_4107_);
lean_closure_set(v___f_4108_, 3, v___x_4096_);
v___x_4109_ = lean_unsigned_to_nat(1u);
v___x_4110_ = lean_mk_empty_array_with_capacity(v___x_4109_);
v___x_4111_ = lean_array_push(v___x_4110_, v_a_4107_);
v___x_4112_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4111_, v_givenNames_4098_, v___f_4108_, v_config_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
return v___x_4112_;
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v_givenNames_4098_);
lean_dec_ref(v___x_4097_);
lean_dec(v___x_4096_);
lean_dec(v_mvarId_4095_);
v_a_4113_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4106_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4106_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
else
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
lean_dec(v_givenNames_4098_);
lean_dec_ref(v___x_4097_);
lean_dec(v___x_4096_);
lean_dec(v_mvarId_4095_);
v_a_4121_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_4105_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4105_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4129_, lean_object* v___x_4130_, lean_object* v___x_4131_, lean_object* v_givenNames_4132_, lean_object* v_config_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4129_, v___x_4130_, v___x_4131_, v_givenNames_4132_, v_config_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec_ref(v_config_4133_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4143_, lean_object* v_givenNames_4144_, lean_object* v_config_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___f_4153_; lean_object* v___x_4154_; 
v___x_4151_ = l_Lean_instInhabitedExpr;
v___x_4152_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4143_);
v___f_4153_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4153_, 0, v_mvarId_4143_);
lean_closure_set(v___f_4153_, 1, v___x_4152_);
lean_closure_set(v___f_4153_, 2, v___x_4151_);
lean_closure_set(v___f_4153_, 3, v_givenNames_4144_);
lean_closure_set(v___f_4153_, 4, v_config_4145_);
v___x_4154_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4143_, v___f_4153_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4155_, lean_object* v_givenNames_4156_, lean_object* v_config_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_MVarId_extractLets(v_mvarId_4155_, v_givenNames_4156_, v_config_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4164_, lean_object* v_val_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4164_, v_val_4165_, v___y_4167_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4172_, lean_object* v_val_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4172_, v_val_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4180_, lean_object* v_x_4181_, lean_object* v_x_4182_, lean_object* v_x_4183_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4181_, v_x_4182_, v_x_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4185_, lean_object* v_x_4186_, size_t v_x_4187_, size_t v_x_4188_, lean_object* v_x_4189_, lean_object* v_x_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4186_, v_x_4187_, v_x_4188_, v_x_4189_, v_x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4192_, lean_object* v_x_4193_, lean_object* v_x_4194_, lean_object* v_x_4195_, lean_object* v_x_4196_, lean_object* v_x_4197_){
_start:
{
size_t v_x_2783__boxed_4198_; size_t v_x_2784__boxed_4199_; lean_object* v_res_4200_; 
v_x_2783__boxed_4198_ = lean_unbox_usize(v_x_4194_);
lean_dec(v_x_4194_);
v_x_2784__boxed_4199_ = lean_unbox_usize(v_x_4195_);
lean_dec(v_x_4195_);
v_res_4200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4192_, v_x_4193_, v_x_2783__boxed_4198_, v_x_2784__boxed_4199_, v_x_4196_, v_x_4197_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4201_, lean_object* v_n_4202_, lean_object* v_k_4203_, lean_object* v_v_4204_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4202_, v_k_4203_, v_v_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4206_, size_t v_depth_4207_, lean_object* v_keys_4208_, lean_object* v_vals_4209_, lean_object* v_heq_4210_, lean_object* v_i_4211_, lean_object* v_entries_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4207_, v_keys_4208_, v_vals_4209_, v_i_4211_, v_entries_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4214_, lean_object* v_depth_4215_, lean_object* v_keys_4216_, lean_object* v_vals_4217_, lean_object* v_heq_4218_, lean_object* v_i_4219_, lean_object* v_entries_4220_){
_start:
{
size_t v_depth_boxed_4221_; lean_object* v_res_4222_; 
v_depth_boxed_4221_ = lean_unbox_usize(v_depth_4215_);
lean_dec(v_depth_4215_);
v_res_4222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4214_, v_depth_boxed_4221_, v_keys_4216_, v_vals_4217_, v_heq_4218_, v_i_4219_, v_entries_4220_);
lean_dec_ref(v_vals_4217_);
lean_dec_ref(v_keys_4216_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4223_, lean_object* v_x_4224_, lean_object* v_x_4225_, lean_object* v_x_4226_, lean_object* v_x_4227_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4224_, v_x_4225_, v_x_4226_, v_x_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4229_, size_t v_i_4230_, lean_object* v_bs_4231_){
_start:
{
uint8_t v___x_4232_; 
v___x_4232_ = lean_usize_dec_lt(v_i_4230_, v_sz_4229_);
if (v___x_4232_ == 0)
{
return v_bs_4231_;
}
else
{
lean_object* v_v_4233_; lean_object* v___x_4234_; lean_object* v_bs_x27_4235_; lean_object* v___x_4236_; size_t v___x_4237_; size_t v___x_4238_; lean_object* v___x_4239_; 
v_v_4233_ = lean_array_uget(v_bs_4231_, v_i_4230_);
v___x_4234_ = lean_unsigned_to_nat(0u);
v_bs_x27_4235_ = lean_array_uset(v_bs_4231_, v_i_4230_, v___x_4234_);
v___x_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4236_, 0, v_v_4233_);
v___x_4237_ = ((size_t)1ULL);
v___x_4238_ = lean_usize_add(v_i_4230_, v___x_4237_);
v___x_4239_ = lean_array_uset(v_bs_x27_4235_, v_i_4230_, v___x_4236_);
v_i_4230_ = v___x_4238_;
v_bs_4231_ = v___x_4239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4241_, lean_object* v_i_4242_, lean_object* v_bs_4243_){
_start:
{
size_t v_sz_boxed_4244_; size_t v_i_boxed_4245_; lean_object* v_res_4246_; 
v_sz_boxed_4244_ = lean_unbox_usize(v_sz_4241_);
lean_dec(v_sz_4241_);
v_i_boxed_4245_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4244_, v_i_boxed_4245_, v_bs_4243_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4247_, lean_object* v_fvars_4248_, lean_object* v_fvarIds_4249_, lean_object* v_givenNames_x27_4250_, lean_object* v_targetNew_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; 
lean_inc(v_mvarId_4247_);
v___x_4257_ = l_Lean_MVarId_getTag(v_mvarId_4247_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4259_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___x_4257_, 1);
v___x_4259_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4251_, v_a_4258_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; size_t v_sz_4261_; size_t v___x_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; uint8_t v___x_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc_n(v_a_4260_, 2);
lean_dec_ref_known(v___x_4259_, 1);
v_sz_4261_ = lean_array_size(v_fvarIds_4249_);
v___x_4262_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4249_);
v___x_4263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4261_, v___x_4262_, v_fvarIds_4249_);
v___x_4264_ = 0;
v___x_4265_ = 1;
v___x_4266_ = 1;
v___x_4267_ = l_Lean_Meta_mkLetFVars(v___x_4263_, v_a_4260_, v___x_4264_, v___x_4265_, v___x_4266_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec_ref(v___x_4263_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v___x_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4282_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v___x_4267_, 1);
v___x_4269_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4247_, v_a_4268_, v___y_4253_);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4282_ == 0)
{
lean_object* v_unused_4283_; 
v_unused_4283_ = lean_ctor_get(v___x_4269_, 0);
lean_dec(v_unused_4283_);
v___x_4271_ = v___x_4269_;
v_isShared_4272_ = v_isSharedCheck_4282_;
goto v_resetjp_4270_;
}
else
{
lean_dec(v___x_4269_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4282_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; size_t v_sz_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4280_; 
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v_fvarIds_4249_);
lean_ctor_set(v___x_4273_, 1, v_givenNames_x27_4250_);
v_sz_4274_ = lean_array_size(v_fvars_4248_);
v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4274_, v___x_4262_, v_fvars_4248_);
v___x_4276_ = l_Lean_Expr_mvarId_x21(v_a_4260_);
lean_dec(v_a_4260_);
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4275_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4273_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4278_);
v___x_4280_ = v___x_4271_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec(v_a_4260_);
lean_dec(v_givenNames_x27_4250_);
lean_dec_ref(v_fvarIds_4249_);
lean_dec_ref(v_fvars_4248_);
lean_dec(v_mvarId_4247_);
v_a_4284_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4267_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4267_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec(v_givenNames_x27_4250_);
lean_dec_ref(v_fvarIds_4249_);
lean_dec_ref(v_fvars_4248_);
lean_dec(v_mvarId_4247_);
v_a_4292_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4259_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4259_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref(v_targetNew_4251_);
lean_dec(v_givenNames_x27_4250_);
lean_dec_ref(v_fvarIds_4249_);
lean_dec_ref(v_fvars_4248_);
lean_dec(v_mvarId_4247_);
v_a_4300_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4257_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4257_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4308_, lean_object* v_fvars_4309_, lean_object* v_fvarIds_4310_, lean_object* v_givenNames_x27_4311_, lean_object* v_targetNew_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4308_, v_fvars_4309_, v_fvarIds_4310_, v_givenNames_x27_4311_, v_targetNew_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4319_, lean_object* v_binderName_4320_, lean_object* v_body_4321_, uint8_t v_binderInfo_4322_, lean_object* v___f_4323_, lean_object* v_binderType_4324_, lean_object* v___x_4325_, lean_object* v_mvarId_4326_, lean_object* v_fvarIds_4327_, lean_object* v_es_4328_, lean_object* v_givenNames_x27_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4335_ = lean_unsigned_to_nat(0u);
v___x_4336_ = lean_array_get_borrowed(v___x_4319_, v_es_4328_, v___x_4335_);
v___x_4340_ = lean_array_get_size(v_fvarIds_4327_);
v___x_4341_ = lean_nat_dec_eq(v___x_4340_, v___x_4335_);
if (v___x_4341_ == 0)
{
lean_dec(v_mvarId_4326_);
lean_dec(v___x_4325_);
goto v___jp_4337_;
}
else
{
uint8_t v___x_4342_; 
v___x_4342_ = lean_expr_eqv(v_binderType_4324_, v___x_4336_);
if (v___x_4342_ == 0)
{
lean_dec(v_mvarId_4326_);
lean_dec(v___x_4325_);
goto v___jp_4337_;
}
else
{
lean_object* v___x_4343_; 
v___x_4343_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4325_, v_mvarId_4326_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_dec_ref_known(v___x_4343_, 1);
goto v___jp_4337_;
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_givenNames_x27_4329_);
lean_dec_ref(v_fvarIds_4327_);
lean_dec_ref(v___f_4323_);
lean_dec_ref(v_body_4321_);
lean_dec(v_binderName_4320_);
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4343_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4343_);
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
}
v___jp_4337_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
lean_inc(v___x_4336_);
v___x_4338_ = l_Lean_Expr_forallE___override(v_binderName_4320_, v___x_4336_, v_body_4321_, v_binderInfo_4322_);
lean_inc(v___y_4333_);
lean_inc_ref(v___y_4332_);
lean_inc(v___y_4331_);
lean_inc_ref(v___y_4330_);
v___x_4339_ = lean_apply_8(v___f_4323_, v_fvarIds_4327_, v_givenNames_x27_4329_, v___x_4338_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, lean_box(0));
return v___x_4339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4352_, lean_object* v_binderName_4353_, lean_object* v_body_4354_, lean_object* v_binderInfo_4355_, lean_object* v___f_4356_, lean_object* v_binderType_4357_, lean_object* v___x_4358_, lean_object* v_mvarId_4359_, lean_object* v_fvarIds_4360_, lean_object* v_es_4361_, lean_object* v_givenNames_x27_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
uint8_t v_binderInfo_1795__boxed_4368_; lean_object* v_res_4369_; 
v_binderInfo_1795__boxed_4368_ = lean_unbox(v_binderInfo_4355_);
v_res_4369_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4352_, v_binderName_4353_, v_body_4354_, v_binderInfo_1795__boxed_4368_, v___f_4356_, v_binderType_4357_, v___x_4358_, v_mvarId_4359_, v_fvarIds_4360_, v_es_4361_, v_givenNames_x27_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v_es_4361_);
lean_dec_ref(v_binderType_4357_);
lean_dec_ref(v___x_4352_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4370_, lean_object* v_declName_4371_, lean_object* v_body_4372_, uint8_t v_nondep_4373_, lean_object* v___f_4374_, lean_object* v_type_4375_, lean_object* v_value_4376_, lean_object* v___x_4377_, lean_object* v_mvarId_4378_, lean_object* v_fvarIds_4379_, lean_object* v_es_4380_, lean_object* v_givenNames_x27_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4387_ = lean_unsigned_to_nat(0u);
v___x_4388_ = lean_array_get_borrowed(v___x_4370_, v_es_4380_, v___x_4387_);
v___x_4389_ = lean_unsigned_to_nat(1u);
v___x_4390_ = lean_array_get_borrowed(v___x_4370_, v_es_4380_, v___x_4389_);
v___x_4394_ = lean_array_get_size(v_fvarIds_4379_);
v___x_4395_ = lean_nat_dec_eq(v___x_4394_, v___x_4387_);
if (v___x_4395_ == 0)
{
lean_dec(v_mvarId_4378_);
lean_dec(v___x_4377_);
goto v___jp_4391_;
}
else
{
uint8_t v___x_4396_; 
v___x_4396_ = lean_expr_eqv(v_type_4375_, v___x_4388_);
if (v___x_4396_ == 0)
{
lean_dec(v_mvarId_4378_);
lean_dec(v___x_4377_);
goto v___jp_4391_;
}
else
{
uint8_t v___x_4397_; 
v___x_4397_ = lean_expr_eqv(v_value_4376_, v___x_4390_);
if (v___x_4397_ == 0)
{
lean_dec(v_mvarId_4378_);
lean_dec(v___x_4377_);
goto v___jp_4391_;
}
else
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4377_, v_mvarId_4378_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_dec_ref_known(v___x_4398_, 1);
goto v___jp_4391_;
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_givenNames_x27_4381_);
lean_dec_ref(v_fvarIds_4379_);
lean_dec_ref(v___f_4374_);
lean_dec_ref(v_body_4372_);
lean_dec(v_declName_4371_);
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
v___jp_4391_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; 
lean_inc(v___x_4390_);
lean_inc(v___x_4388_);
v___x_4392_ = l_Lean_Expr_letE___override(v_declName_4371_, v___x_4388_, v___x_4390_, v_body_4372_, v_nondep_4373_);
lean_inc(v___y_4385_);
lean_inc_ref(v___y_4384_);
lean_inc(v___y_4383_);
lean_inc_ref(v___y_4382_);
v___x_4393_ = lean_apply_8(v___f_4374_, v_fvarIds_4379_, v_givenNames_x27_4381_, v___x_4392_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, lean_box(0));
return v___x_4393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4407_ = _args[0];
lean_object* v_declName_4408_ = _args[1];
lean_object* v_body_4409_ = _args[2];
lean_object* v_nondep_4410_ = _args[3];
lean_object* v___f_4411_ = _args[4];
lean_object* v_type_4412_ = _args[5];
lean_object* v_value_4413_ = _args[6];
lean_object* v___x_4414_ = _args[7];
lean_object* v_mvarId_4415_ = _args[8];
lean_object* v_fvarIds_4416_ = _args[9];
lean_object* v_es_4417_ = _args[10];
lean_object* v_givenNames_x27_4418_ = _args[11];
lean_object* v___y_4419_ = _args[12];
lean_object* v___y_4420_ = _args[13];
lean_object* v___y_4421_ = _args[14];
lean_object* v___y_4422_ = _args[15];
lean_object* v___y_4423_ = _args[16];
_start:
{
uint8_t v_nondep_1866__boxed_4424_; lean_object* v_res_4425_; 
v_nondep_1866__boxed_4424_ = lean_unbox(v_nondep_4410_);
v_res_4425_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4407_, v_declName_4408_, v_body_4409_, v_nondep_1866__boxed_4424_, v___f_4411_, v_type_4412_, v_value_4413_, v___x_4414_, v_mvarId_4415_, v_fvarIds_4416_, v_es_4417_, v_givenNames_x27_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec_ref(v_es_4417_);
lean_dec_ref(v_value_4413_);
lean_dec_ref(v_type_4412_);
lean_dec_ref(v___x_4407_);
return v_res_4425_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4430_ = l_Lean_MessageData_ofFormat(v___x_4429_);
return v___x_4430_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4433_, lean_object* v___x_4434_, lean_object* v___f_4435_, lean_object* v___x_4436_, lean_object* v_givenNames_4437_, lean_object* v_config_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
lean_inc(v_mvarId_4433_);
v___x_4444_ = l_Lean_MVarId_getType(v_mvarId_4433_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4445_);
lean_dec_ref_known(v___x_4444_, 1);
switch(lean_obj_tag(v_a_4445_))
{
case 7:
{
lean_object* v_binderName_4446_; lean_object* v_binderType_4447_; lean_object* v_body_4448_; uint8_t v_binderInfo_4449_; lean_object* v___x_4450_; lean_object* v___f_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_binderName_4446_ = lean_ctor_get(v_a_4445_, 0);
lean_inc(v_binderName_4446_);
v_binderType_4447_ = lean_ctor_get(v_a_4445_, 1);
lean_inc_ref_n(v_binderType_4447_, 2);
v_body_4448_ = lean_ctor_get(v_a_4445_, 2);
lean_inc_ref(v_body_4448_);
v_binderInfo_4449_ = lean_ctor_get_uint8(v_a_4445_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4445_, 3);
v___x_4450_ = lean_box(v_binderInfo_4449_);
v___f_4451_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4451_, 0, v___x_4434_);
lean_closure_set(v___f_4451_, 1, v_binderName_4446_);
lean_closure_set(v___f_4451_, 2, v_body_4448_);
lean_closure_set(v___f_4451_, 3, v___x_4450_);
lean_closure_set(v___f_4451_, 4, v___f_4435_);
lean_closure_set(v___f_4451_, 5, v_binderType_4447_);
lean_closure_set(v___f_4451_, 6, v___x_4436_);
lean_closure_set(v___f_4451_, 7, v_mvarId_4433_);
v___x_4452_ = lean_unsigned_to_nat(1u);
v___x_4453_ = lean_mk_empty_array_with_capacity(v___x_4452_);
v___x_4454_ = lean_array_push(v___x_4453_, v_binderType_4447_);
v___x_4455_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4454_, v_givenNames_4437_, v___f_4451_, v_config_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
return v___x_4455_;
}
case 8:
{
lean_object* v_declName_4456_; lean_object* v_type_4457_; lean_object* v_value_4458_; lean_object* v_body_4459_; uint8_t v_nondep_4460_; lean_object* v___x_4461_; lean_object* v___f_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v_declName_4456_ = lean_ctor_get(v_a_4445_, 0);
lean_inc(v_declName_4456_);
v_type_4457_ = lean_ctor_get(v_a_4445_, 1);
lean_inc_ref_n(v_type_4457_, 2);
v_value_4458_ = lean_ctor_get(v_a_4445_, 2);
lean_inc_ref_n(v_value_4458_, 2);
v_body_4459_ = lean_ctor_get(v_a_4445_, 3);
lean_inc_ref(v_body_4459_);
v_nondep_4460_ = lean_ctor_get_uint8(v_a_4445_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4445_, 4);
v___x_4461_ = lean_box(v_nondep_4460_);
v___f_4462_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4462_, 0, v___x_4434_);
lean_closure_set(v___f_4462_, 1, v_declName_4456_);
lean_closure_set(v___f_4462_, 2, v_body_4459_);
lean_closure_set(v___f_4462_, 3, v___x_4461_);
lean_closure_set(v___f_4462_, 4, v___f_4435_);
lean_closure_set(v___f_4462_, 5, v_type_4457_);
lean_closure_set(v___f_4462_, 6, v_value_4458_);
lean_closure_set(v___f_4462_, 7, v___x_4436_);
lean_closure_set(v___f_4462_, 8, v_mvarId_4433_);
v___x_4463_ = lean_unsigned_to_nat(2u);
v___x_4464_ = lean_mk_empty_array_with_capacity(v___x_4463_);
v___x_4465_ = lean_array_push(v___x_4464_, v_type_4457_);
v___x_4466_ = lean_array_push(v___x_4465_, v_value_4458_);
v___x_4467_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4466_, v_givenNames_4437_, v___f_4462_, v_config_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
return v___x_4467_;
}
default: 
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_dec(v_a_4445_);
lean_dec(v_givenNames_4437_);
lean_dec_ref(v___f_4435_);
lean_dec_ref(v___x_4434_);
v___x_4468_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4469_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4436_, v_mvarId_4433_, v___x_4468_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
return v___x_4469_;
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_givenNames_4437_);
lean_dec(v___x_4436_);
lean_dec_ref(v___f_4435_);
lean_dec_ref(v___x_4434_);
lean_dec(v_mvarId_4433_);
v_a_4470_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4444_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4444_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4478_, lean_object* v___x_4479_, lean_object* v___f_4480_, lean_object* v___x_4481_, lean_object* v_givenNames_4482_, lean_object* v_config_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4478_, v___x_4479_, v___f_4480_, v___x_4481_, v_givenNames_4482_, v_config_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec_ref(v_config_4483_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4490_, lean_object* v___x_4491_, lean_object* v_givenNames_4492_, lean_object* v_config_4493_, lean_object* v_mvarId_4494_, lean_object* v_fvars_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___f_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; 
lean_inc_n(v_mvarId_4494_, 2);
v___f_4501_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4501_, 0, v_mvarId_4494_);
lean_closure_set(v___f_4501_, 1, v_fvars_4495_);
v___f_4502_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4502_, 0, v_mvarId_4494_);
lean_closure_set(v___f_4502_, 1, v___x_4490_);
lean_closure_set(v___f_4502_, 2, v___f_4501_);
lean_closure_set(v___f_4502_, 3, v___x_4491_);
lean_closure_set(v___f_4502_, 4, v_givenNames_4492_);
lean_closure_set(v___f_4502_, 5, v_config_4493_);
v___x_4503_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4494_, v___f_4502_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4504_, lean_object* v___x_4505_, lean_object* v_givenNames_4506_, lean_object* v_config_4507_, lean_object* v_mvarId_4508_, lean_object* v_fvars_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4504_, v___x_4505_, v_givenNames_4506_, v_config_4507_, v_mvarId_4508_, v_fvars_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4516_, lean_object* v_fvarId_4517_, lean_object* v_givenNames_4518_, lean_object* v_config_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4516_);
v___x_4526_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4516_, v___x_4525_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v___x_4527_; lean_object* v___f_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; lean_object* v___x_4533_; 
lean_dec_ref_known(v___x_4526_, 1);
v___x_4527_ = l_Lean_instInhabitedExpr;
v___f_4528_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4528_, 0, v___x_4527_);
lean_closure_set(v___f_4528_, 1, v___x_4525_);
lean_closure_set(v___f_4528_, 2, v_givenNames_4518_);
lean_closure_set(v___f_4528_, 3, v_config_4519_);
v___x_4529_ = lean_unsigned_to_nat(1u);
v___x_4530_ = lean_mk_empty_array_with_capacity(v___x_4529_);
v___x_4531_ = lean_array_push(v___x_4530_, v_fvarId_4517_);
v___x_4532_ = 0;
v___x_4533_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4516_, v___x_4531_, v___f_4528_, v___x_4532_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
return v___x_4533_;
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v_config_4519_);
lean_dec(v_givenNames_4518_);
lean_dec(v_fvarId_4517_);
lean_dec(v_mvarId_4516_);
v_a_4534_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4526_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4526_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4542_, lean_object* v_fvarId_4543_, lean_object* v_givenNames_4544_, lean_object* v_config_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4542_, v_fvarId_4543_, v_givenNames_4544_, v_config_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4552_, lean_object* v___x_4553_, lean_object* v_config_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; 
lean_inc(v___x_4553_);
lean_inc(v_mvarId_4552_);
v___x_4560_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4552_, v___x_4553_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v___x_4561_; 
lean_dec_ref_known(v___x_4560_, 1);
lean_inc(v_mvarId_4552_);
v___x_4561_ = l_Lean_MVarId_getType(v_mvarId_4552_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4563_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc_n(v_a_4562_, 2);
lean_dec_ref_known(v___x_4561_, 1);
v___x_4563_ = l_Lean_Meta_liftLets(v_a_4562_, v_config_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; uint8_t v___x_4565_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4565_ = lean_expr_eqv(v_a_4562_, v_a_4564_);
lean_dec(v_a_4562_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
lean_dec(v___x_4553_);
v___x_4566_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4552_, v_a_4564_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; 
lean_inc(v_mvarId_4552_);
v___x_4567_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4553_, v_mvarId_4552_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v___x_4568_; 
lean_dec_ref_known(v___x_4567_, 1);
v___x_4568_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4552_, v_a_4564_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4568_;
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec(v_a_4564_);
lean_dec(v_mvarId_4552_);
v_a_4569_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4567_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4567_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec(v_a_4562_);
lean_dec(v___x_4553_);
lean_dec(v_mvarId_4552_);
v_a_4577_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4563_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4563_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_config_4554_);
lean_dec(v___x_4553_);
lean_dec(v_mvarId_4552_);
v_a_4585_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4561_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4561_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec_ref(v_config_4554_);
lean_dec(v___x_4553_);
lean_dec(v_mvarId_4552_);
v_a_4593_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4560_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4560_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4601_, lean_object* v___x_4602_, lean_object* v_config_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4601_, v___x_4602_, v_config_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4613_, lean_object* v_config_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v___x_4620_; lean_object* v___f_4621_; lean_object* v___x_4622_; 
v___x_4620_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4613_);
v___f_4621_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4621_, 0, v_mvarId_4613_);
lean_closure_set(v___f_4621_, 1, v___x_4620_);
lean_closure_set(v___f_4621_, 2, v_config_4614_);
v___x_4622_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4613_, v___f_4621_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4623_, lean_object* v_config_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Lean_MVarId_liftLets(v_mvarId_4623_, v_config_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4631_, lean_object* v_fvars_4632_, lean_object* v_targetNew_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4631_, v_targetNew_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4653_; 
v_a_4640_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4642_ = v___x_4639_;
v_isShared_4643_ = v_isSharedCheck_4653_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4639_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4653_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4644_; size_t v_sz_4645_; size_t v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4651_; 
v___x_4644_ = lean_box(0);
v_sz_4645_ = lean_array_size(v_fvars_4632_);
v___x_4646_ = ((size_t)0ULL);
v___x_4647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4645_, v___x_4646_, v_fvars_4632_);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v_a_4640_);
v___x_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4644_);
lean_ctor_set(v___x_4649_, 1, v___x_4648_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 0, v___x_4649_);
v___x_4651_ = v___x_4642_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v_fvars_4632_);
v_a_4654_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4639_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4639_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4662_, lean_object* v_fvars_4663_, lean_object* v_targetNew_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4662_, v_fvars_4663_, v_targetNew_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4671_, lean_object* v_config_4672_, lean_object* v___f_4673_, lean_object* v___x_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___x_4680_; 
lean_inc(v_mvarId_4671_);
v___x_4680_ = l_Lean_MVarId_getType(v_mvarId_4671_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v___x_4680_, 1);
switch(lean_obj_tag(v_a_4681_))
{
case 7:
{
lean_object* v_binderName_4682_; lean_object* v_binderType_4683_; lean_object* v_body_4684_; uint8_t v_binderInfo_4685_; lean_object* v___x_4686_; 
v_binderName_4682_ = lean_ctor_get(v_a_4681_, 0);
lean_inc(v_binderName_4682_);
v_binderType_4683_ = lean_ctor_get(v_a_4681_, 1);
lean_inc_ref_n(v_binderType_4683_, 2);
v_body_4684_ = lean_ctor_get(v_a_4681_, 2);
lean_inc_ref(v_body_4684_);
v_binderInfo_4685_ = lean_ctor_get_uint8(v_a_4681_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4681_, 3);
v___x_4686_ = l_Lean_Meta_liftLets(v_binderType_4683_, v_config_4672_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; uint8_t v___x_4695_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
v___x_4695_ = lean_expr_eqv(v_binderType_4683_, v_a_4687_);
lean_dec_ref(v_binderType_4683_);
if (v___x_4695_ == 0)
{
lean_dec(v___x_4674_);
lean_dec(v_mvarId_4671_);
v___y_4689_ = v___y_4675_;
v___y_4690_ = v___y_4676_;
v___y_4691_ = v___y_4677_;
v___y_4692_ = v___y_4678_;
goto v___jp_4688_;
}
else
{
lean_object* v___x_4696_; 
v___x_4696_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4674_, v_mvarId_4671_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_dec_ref_known(v___x_4696_, 1);
v___y_4689_ = v___y_4675_;
v___y_4690_ = v___y_4676_;
v___y_4691_ = v___y_4677_;
v___y_4692_ = v___y_4678_;
goto v___jp_4688_;
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec(v_a_4687_);
lean_dec_ref(v_body_4684_);
lean_dec(v_binderName_4682_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec_ref(v___f_4673_);
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4696_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
v___jp_4688_:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4693_ = l_Lean_Expr_forallE___override(v_binderName_4682_, v_a_4687_, v_body_4684_, v_binderInfo_4685_);
v___x_4694_ = lean_apply_6(v___f_4673_, v___x_4693_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, lean_box(0));
return v___x_4694_;
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref(v_body_4684_);
lean_dec_ref(v_binderType_4683_);
lean_dec(v_binderName_4682_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___x_4674_);
lean_dec_ref(v___f_4673_);
lean_dec(v_mvarId_4671_);
v_a_4705_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4686_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4686_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
case 8:
{
lean_object* v_declName_4713_; lean_object* v_type_4714_; lean_object* v_value_4715_; lean_object* v_body_4716_; uint8_t v_nondep_4717_; lean_object* v___x_4718_; 
v_declName_4713_ = lean_ctor_get(v_a_4681_, 0);
lean_inc(v_declName_4713_);
v_type_4714_ = lean_ctor_get(v_a_4681_, 1);
lean_inc_ref_n(v_type_4714_, 2);
v_value_4715_ = lean_ctor_get(v_a_4681_, 2);
lean_inc_ref(v_value_4715_);
v_body_4716_ = lean_ctor_get(v_a_4681_, 3);
lean_inc_ref(v_body_4716_);
v_nondep_4717_ = lean_ctor_get_uint8(v_a_4681_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4681_, 4);
lean_inc_ref(v_config_4672_);
v___x_4718_ = l_Lean_Meta_liftLets(v_type_4714_, v_config_4672_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4720_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4718_, 1);
lean_inc_ref(v_value_4715_);
v___x_4720_ = l_Lean_Meta_liftLets(v_value_4715_, v_config_4672_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; uint8_t v___y_4730_; uint8_t v___x_4740_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v___x_4740_ = lean_expr_eqv(v_type_4714_, v_a_4719_);
lean_dec_ref(v_type_4714_);
if (v___x_4740_ == 0)
{
lean_dec_ref(v_value_4715_);
v___y_4730_ = v___x_4740_;
goto v___jp_4729_;
}
else
{
uint8_t v___x_4741_; 
v___x_4741_ = lean_expr_eqv(v_value_4715_, v_a_4721_);
lean_dec_ref(v_value_4715_);
v___y_4730_ = v___x_4741_;
goto v___jp_4729_;
}
v___jp_4722_:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4727_ = l_Lean_Expr_letE___override(v_declName_4713_, v_a_4719_, v_a_4721_, v_body_4716_, v_nondep_4717_);
v___x_4728_ = lean_apply_6(v___f_4673_, v___x_4727_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, lean_box(0));
return v___x_4728_;
}
v___jp_4729_:
{
if (v___y_4730_ == 0)
{
lean_dec(v___x_4674_);
lean_dec(v_mvarId_4671_);
v___y_4723_ = v___y_4675_;
v___y_4724_ = v___y_4676_;
v___y_4725_ = v___y_4677_;
v___y_4726_ = v___y_4678_;
goto v___jp_4722_;
}
else
{
lean_object* v___x_4731_; 
v___x_4731_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4674_, v_mvarId_4671_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_dec_ref_known(v___x_4731_, 1);
v___y_4723_ = v___y_4675_;
v___y_4724_ = v___y_4676_;
v___y_4725_ = v___y_4677_;
v___y_4726_ = v___y_4678_;
goto v___jp_4722_;
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_dec(v_a_4721_);
lean_dec(v_a_4719_);
lean_dec_ref(v_body_4716_);
lean_dec(v_declName_4713_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec_ref(v___f_4673_);
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec(v_a_4719_);
lean_dec_ref(v_body_4716_);
lean_dec_ref(v_value_4715_);
lean_dec_ref(v_type_4714_);
lean_dec(v_declName_4713_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___x_4674_);
lean_dec_ref(v___f_4673_);
lean_dec(v_mvarId_4671_);
v_a_4742_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4720_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4720_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec_ref(v_body_4716_);
lean_dec_ref(v_value_4715_);
lean_dec_ref(v_type_4714_);
lean_dec(v_declName_4713_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___x_4674_);
lean_dec_ref(v___f_4673_);
lean_dec_ref(v_config_4672_);
lean_dec(v_mvarId_4671_);
v_a_4750_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4718_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4718_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
default: 
{
lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec(v_a_4681_);
lean_dec_ref(v___f_4673_);
lean_dec_ref(v_config_4672_);
v___x_4758_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4759_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4674_, v_mvarId_4671_, v___x_4758_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
return v___x_4759_;
}
}
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___x_4674_);
lean_dec_ref(v___f_4673_);
lean_dec_ref(v_config_4672_);
lean_dec(v_mvarId_4671_);
v_a_4760_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4680_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4680_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4768_, lean_object* v_config_4769_, lean_object* v___f_4770_, lean_object* v___x_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4768_, v_config_4769_, v___f_4770_, v___x_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4778_, lean_object* v___x_4779_, lean_object* v_mvarId_4780_, lean_object* v_fvars_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v___f_4787_; lean_object* v___f_4788_; lean_object* v___x_4789_; 
lean_inc_n(v_mvarId_4780_, 2);
v___f_4787_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4787_, 0, v_mvarId_4780_);
lean_closure_set(v___f_4787_, 1, v_fvars_4781_);
v___f_4788_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4788_, 0, v_mvarId_4780_);
lean_closure_set(v___f_4788_, 1, v_config_4778_);
lean_closure_set(v___f_4788_, 2, v___f_4787_);
lean_closure_set(v___f_4788_, 3, v___x_4779_);
v___x_4789_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4780_, v___f_4788_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4790_, lean_object* v___x_4791_, lean_object* v_mvarId_4792_, lean_object* v_fvars_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4790_, v___x_4791_, v_mvarId_4792_, v_fvars_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4800_, lean_object* v_fvarId_4801_, lean_object* v_config_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_){
_start:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4800_);
v___x_4809_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4800_, v___x_4808_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v___f_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; lean_object* v___x_4815_; 
lean_dec_ref_known(v___x_4809_, 1);
v___f_4810_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4810_, 0, v_config_4802_);
lean_closure_set(v___f_4810_, 1, v___x_4808_);
v___x_4811_ = lean_unsigned_to_nat(1u);
v___x_4812_ = lean_mk_empty_array_with_capacity(v___x_4811_);
v___x_4813_ = lean_array_push(v___x_4812_, v_fvarId_4801_);
v___x_4814_ = 0;
v___x_4815_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4800_, v___x_4813_, v___f_4810_, v___x_4814_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4824_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4818_ = v___x_4815_;
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4815_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v_snd_4820_; lean_object* v___x_4822_; 
v_snd_4820_ = lean_ctor_get(v_a_4816_, 1);
lean_inc(v_snd_4820_);
lean_dec(v_a_4816_);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 0, v_snd_4820_);
v___x_4822_ = v___x_4818_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_snd_4820_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
v_a_4825_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4815_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4815_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_dec_ref(v_config_4802_);
lean_dec(v_fvarId_4801_);
lean_dec(v_mvarId_4800_);
v_a_4833_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4809_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4809_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4841_, lean_object* v_fvarId_4842_, lean_object* v_config_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4841_, v_fvarId_4842_, v_config_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4850_, lean_object* v___x_4851_, uint8_t v_failIfUnchanged_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v___x_4858_; 
lean_inc(v___x_4851_);
lean_inc(v_mvarId_4850_);
v___x_4858_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4850_, v___x_4851_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v___x_4859_; 
lean_dec_ref_known(v___x_4858_, 1);
lean_inc(v_mvarId_4850_);
v___x_4859_ = l_Lean_MVarId_getType(v_mvarId_4850_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4861_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc_n(v_a_4860_, 2);
lean_dec_ref_known(v___x_4859_, 1);
v___x_4861_ = l_Lean_Meta_letToHave(v_a_4860_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4861_) == 0)
{
if (v_failIfUnchanged_4852_ == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4863_; 
lean_dec(v_a_4860_);
lean_dec(v___x_4851_);
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4863_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4850_, v_a_4862_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
return v___x_4863_;
}
else
{
lean_object* v_a_4864_; uint8_t v___x_4865_; 
v_a_4864_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4865_ = lean_expr_eqv(v_a_4860_, v_a_4864_);
lean_dec(v_a_4860_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4866_; 
lean_dec(v___x_4851_);
v___x_4866_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4850_, v_a_4864_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
return v___x_4866_;
}
else
{
lean_object* v___x_4867_; 
lean_inc(v_mvarId_4850_);
v___x_4867_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4851_, v_mvarId_4850_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v___x_4868_; 
lean_dec_ref_known(v___x_4867_, 1);
v___x_4868_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4850_, v_a_4864_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
return v___x_4868_;
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v_a_4864_);
lean_dec(v_mvarId_4850_);
v_a_4869_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4867_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4867_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
}
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v_a_4860_);
lean_dec(v___x_4851_);
lean_dec(v_mvarId_4850_);
v_a_4877_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4861_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4861_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec(v___x_4851_);
lean_dec(v_mvarId_4850_);
v_a_4885_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4859_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4859_);
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
lean_dec(v___x_4851_);
lean_dec(v_mvarId_4850_);
v_a_4893_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4858_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4858_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4901_, lean_object* v___x_4902_, lean_object* v_failIfUnchanged_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4909_; lean_object* v_res_4910_; 
v_failIfUnchanged_boxed_4909_ = lean_unbox(v_failIfUnchanged_4903_);
v_res_4910_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4901_, v___x_4902_, v_failIfUnchanged_boxed_4909_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
return v_res_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4914_, uint8_t v_failIfUnchanged_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_){
_start:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___f_4923_; lean_object* v___x_4924_; 
v___x_4921_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4922_ = lean_box(v_failIfUnchanged_4915_);
lean_inc(v_mvarId_4914_);
v___f_4923_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4923_, 0, v_mvarId_4914_);
lean_closure_set(v___f_4923_, 1, v___x_4921_);
lean_closure_set(v___f_4923_, 2, v___x_4922_);
v___x_4924_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4914_, v___f_4923_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4925_, lean_object* v_failIfUnchanged_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4932_; lean_object* v_res_4933_; 
v_failIfUnchanged_boxed_4932_ = lean_unbox(v_failIfUnchanged_4926_);
v_res_4933_ = l_Lean_MVarId_letToHave(v_mvarId_4925_, v_failIfUnchanged_boxed_4932_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4934_, lean_object* v___x_4935_, lean_object* v_fvarId_4936_, uint8_t v_failIfUnchanged_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v___x_4943_; 
lean_inc(v___x_4935_);
lean_inc(v_mvarId_4934_);
v___x_4943_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4934_, v___x_4935_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v___x_4944_; 
lean_dec_ref_known(v___x_4943_, 1);
lean_inc(v_fvarId_4936_);
v___x_4944_ = l_Lean_FVarId_getType___redArg(v_fvarId_4936_, v___y_4938_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4946_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc_n(v_a_4945_, 2);
lean_dec_ref_known(v___x_4944_, 1);
v___x_4946_ = l_Lean_Meta_letToHave(v_a_4945_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4946_) == 0)
{
if (v_failIfUnchanged_4937_ == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4948_; 
lean_dec(v_a_4945_);
lean_dec(v___x_4935_);
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4948_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4934_, v_fvarId_4936_, v_a_4947_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
return v___x_4948_;
}
else
{
lean_object* v_a_4949_; uint8_t v___x_4950_; 
v_a_4949_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4949_);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4950_ = lean_expr_eqv(v_a_4945_, v_a_4949_);
lean_dec(v_a_4945_);
if (v___x_4950_ == 0)
{
lean_object* v___x_4951_; 
lean_dec(v___x_4935_);
v___x_4951_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4934_, v_fvarId_4936_, v_a_4949_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
return v___x_4951_;
}
else
{
lean_object* v___x_4952_; 
lean_inc(v_mvarId_4934_);
v___x_4952_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4935_, v_mvarId_4934_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v___x_4953_; 
lean_dec_ref_known(v___x_4952_, 1);
v___x_4953_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4934_, v_fvarId_4936_, v_a_4949_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
return v___x_4953_;
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec(v_a_4949_);
lean_dec(v_fvarId_4936_);
lean_dec(v_mvarId_4934_);
v_a_4954_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4952_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4952_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
}
else
{
lean_object* v_a_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4969_; 
lean_dec(v_a_4945_);
lean_dec(v_fvarId_4936_);
lean_dec(v___x_4935_);
lean_dec(v_mvarId_4934_);
v_a_4962_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4964_ = v___x_4946_;
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_a_4962_);
lean_dec(v___x_4946_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4967_; 
if (v_isShared_4965_ == 0)
{
v___x_4967_ = v___x_4964_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
}
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_dec(v_fvarId_4936_);
lean_dec(v___x_4935_);
lean_dec(v_mvarId_4934_);
v_a_4970_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4944_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4944_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
else
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
lean_dec(v_fvarId_4936_);
lean_dec(v___x_4935_);
lean_dec(v_mvarId_4934_);
v_a_4978_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4943_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4943_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_4986_, lean_object* v___x_4987_, lean_object* v_fvarId_4988_, lean_object* v_failIfUnchanged_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4995_; lean_object* v_res_4996_; 
v_failIfUnchanged_boxed_4995_ = lean_unbox(v_failIfUnchanged_4989_);
v_res_4996_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_4986_, v___x_4987_, v_fvarId_4988_, v_failIfUnchanged_boxed_4995_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_4997_, lean_object* v_fvarId_4998_, uint8_t v_failIfUnchanged_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___f_5007_; lean_object* v___x_5008_; 
v___x_5005_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5006_ = lean_box(v_failIfUnchanged_4999_);
lean_inc(v_mvarId_4997_);
v___f_5007_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5007_, 0, v_mvarId_4997_);
lean_closure_set(v___f_5007_, 1, v___x_5005_);
lean_closure_set(v___f_5007_, 2, v_fvarId_4998_);
lean_closure_set(v___f_5007_, 3, v___x_5006_);
v___x_5008_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4997_, v___f_5007_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5009_, lean_object* v_fvarId_5010_, lean_object* v_failIfUnchanged_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5017_; lean_object* v_res_5018_; 
v_failIfUnchanged_boxed_5017_ = lean_unbox(v_failIfUnchanged_5011_);
v_res_5018_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5009_, v_fvarId_5010_, v_failIfUnchanged_boxed_5017_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
return v_res_5018_;
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
