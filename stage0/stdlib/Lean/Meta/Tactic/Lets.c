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
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_nbuckets_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_402_ = lean_array_get_size(v_data_401_);
v___x_403_ = lean_unsigned_to_nat(2u);
v_nbuckets_404_ = lean_nat_mul(v___x_402_, v___x_403_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_box(0);
v___x_407_ = lean_mk_array(v_nbuckets_404_, v___x_406_);
v___x_408_ = lean_array_propagate_mark(v_data_401_, v___x_407_);
v___x_409_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v___x_405_, v_data_401_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(lean_object* v_m_410_, lean_object* v_a_411_, lean_object* v_b_412_){
_start:
{
lean_object* v_size_413_; lean_object* v_buckets_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_457_; 
v_size_413_ = lean_ctor_get(v_m_410_, 0);
v_buckets_414_ = lean_ctor_get(v_m_410_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_m_410_);
if (v_isSharedCheck_457_ == 0)
{
v___x_416_ = v_m_410_;
v_isShared_417_ = v_isSharedCheck_457_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_buckets_414_);
lean_inc(v_size_413_);
lean_dec(v_m_410_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_457_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; uint64_t v_fold_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; lean_object* v_bkt_431_; uint8_t v___x_432_; 
v___x_418_ = lean_array_get_size(v_buckets_414_);
v___x_419_ = l_Lean_ExprStructEq_hash(v_a_411_);
v___x_420_ = 32ULL;
v___x_421_ = lean_uint64_shift_right(v___x_419_, v___x_420_);
v_fold_422_ = lean_uint64_xor(v___x_419_, v___x_421_);
v___x_423_ = 16ULL;
v___x_424_ = lean_uint64_shift_right(v_fold_422_, v___x_423_);
v___x_425_ = lean_uint64_xor(v_fold_422_, v___x_424_);
v___x_426_ = lean_uint64_to_usize(v___x_425_);
v___x_427_ = lean_usize_of_nat(v___x_418_);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_sub(v___x_427_, v___x_428_);
v___x_430_ = lean_usize_land(v___x_426_, v___x_429_);
v_bkt_431_ = lean_array_uget_borrowed(v_buckets_414_, v___x_430_);
v___x_432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_411_, v_bkt_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v_size_x27_434_; lean_object* v___x_435_; lean_object* v_buckets_x27_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v_size_x27_434_ = lean_nat_add(v_size_413_, v___x_433_);
lean_dec(v_size_413_);
lean_inc(v_bkt_431_);
v___x_435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_435_, 0, v_a_411_);
lean_ctor_set(v___x_435_, 1, v_b_412_);
lean_ctor_set(v___x_435_, 2, v_bkt_431_);
v_buckets_x27_436_ = lean_array_uset(v_buckets_414_, v___x_430_, v___x_435_);
v___x_437_ = lean_unsigned_to_nat(4u);
v___x_438_ = lean_nat_mul(v_size_x27_434_, v___x_437_);
v___x_439_ = lean_unsigned_to_nat(3u);
v___x_440_ = lean_nat_div(v___x_438_, v___x_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_array_get_size(v_buckets_x27_436_);
v___x_442_ = lean_nat_dec_le(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
if (v___x_442_ == 0)
{
lean_object* v_val_443_; lean_object* v___x_445_; 
v_val_443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_buckets_x27_436_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_val_443_);
lean_ctor_set(v___x_416_, 0, v_size_x27_434_);
v___x_445_ = v___x_416_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_size_x27_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_val_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v___x_448_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_buckets_x27_436_);
lean_ctor_set(v___x_416_, 0, v_size_x27_434_);
v___x_448_ = v___x_416_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_size_x27_434_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_buckets_x27_436_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v___x_450_; lean_object* v_buckets_x27_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
lean_inc(v_bkt_431_);
v___x_450_ = lean_box(0);
v_buckets_x27_451_ = lean_array_uset(v_buckets_414_, v___x_430_, v___x_450_);
v___x_452_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_411_, v_b_412_, v_bkt_431_);
v___x_453_ = lean_array_uset(v_buckets_x27_451_, v___x_430_, v___x_452_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_453_);
v___x_455_ = v___x_416_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_size_413_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg(lean_object* v_decl_458_, uint8_t v_isLet_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v_givenNames_469_; lean_object* v_decls_470_; lean_object* v_valueMap_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_489_; 
v___x_463_ = lean_st_ref_take(v_a_461_);
v_givenNames_469_ = lean_ctor_get(v___x_463_, 0);
v_decls_470_ = lean_ctor_get(v___x_463_, 1);
v_valueMap_471_ = lean_ctor_get(v___x_463_, 2);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_489_ == 0)
{
v___x_473_ = v___x_463_;
v_isShared_474_ = v_isSharedCheck_489_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_valueMap_471_);
lean_inc(v_decls_470_);
lean_inc(v_givenNames_469_);
lean_dec(v___x_463_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_489_;
goto v_resetjp_472_;
}
v___jp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_st_ref_put(v_a_461_, v_snd_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v_fst_465_);
return v___x_468_;
}
v_resetjp_472_:
{
uint8_t v_merge_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_merge_475_ = lean_ctor_get_uint8(v_a_460_, 6);
v___x_476_ = lean_box(0);
lean_inc_ref(v_decl_458_);
v___x_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_477_, 0, v_decl_458_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v_isLet_459_);
v___x_478_ = lean_array_push(v_decls_470_, v___x_477_);
if (v_merge_475_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref(v_decl_458_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_478_);
v___x_480_ = v___x_473_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_givenNames_469_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_valueMap_471_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v_fst_465_ = v___x_476_;
v_snd_466_ = v___x_480_;
goto v___jp_464_;
}
}
else
{
uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_482_ = 0;
v___x_483_ = l_Lean_LocalDecl_value(v_decl_458_, v___x_482_);
v___x_484_ = l_Lean_LocalDecl_fvarId(v_decl_458_);
lean_dec_ref(v_decl_458_);
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_471_, v___x_483_, v___x_484_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v___x_485_);
lean_ctor_set(v___x_473_, 1, v___x_478_);
v___x_487_ = v___x_473_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_givenNames_469_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v_fst_465_ = v___x_476_;
v_snd_466_ = v___x_487_;
goto v___jp_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg___boxed(lean_object* v_decl_490_, lean_object* v_isLet_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
uint8_t v_isLet_boxed_495_; lean_object* v_res_496_; 
v_isLet_boxed_495_ = lean_unbox(v_isLet_491_);
v_res_496_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_490_, v_isLet_boxed_495_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl(lean_object* v_decl_497_, uint8_t v_isLet_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_497_, v_isLet_498_, v_a_499_, v_a_501_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___boxed(lean_object* v_decl_508_, lean_object* v_isLet_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
uint8_t v_isLet_boxed_518_; lean_object* v_res_519_; 
v_isLet_boxed_518_ = lean_unbox(v_isLet_509_);
v_res_519_ = l_Lean_Meta_ExtractLets_addDecl(v_decl_508_, v_isLet_boxed_518_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0(lean_object* v_00_u03b2_520_, lean_object* v_m_521_, lean_object* v_a_522_, lean_object* v_b_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_m_521_, v_a_522_, v_b_523_);
return v___x_524_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(v_00_u03b2_529_, v_a_530_, v_x_531_);
lean_dec(v_x_531_);
lean_dec_ref(v_a_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1(lean_object* v_00_u03b2_534_, lean_object* v_data_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_data_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2(lean_object* v_00_u03b2_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_538_, v_b_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_542_, lean_object* v_i_543_, lean_object* v_source_544_, lean_object* v_target_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v_i_543_, v_source_544_, v_target_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(v_x_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(lean_object* v_k_551_, lean_object* v_t_552_){
_start:
{
if (lean_obj_tag(v_t_552_) == 0)
{
lean_object* v_k_553_; lean_object* v_l_554_; lean_object* v_r_555_; uint8_t v___x_556_; 
v_k_553_ = lean_ctor_get(v_t_552_, 1);
v_l_554_ = lean_ctor_get(v_t_552_, 3);
v_r_555_ = lean_ctor_get(v_t_552_, 4);
v___x_556_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_551_, v_k_553_);
switch(v___x_556_)
{
case 0:
{
v_t_552_ = v_l_554_;
goto _start;
}
case 1:
{
uint8_t v___x_558_; 
v___x_558_ = 1;
return v___x_558_;
}
default: 
{
v_t_552_ = v_r_555_;
goto _start;
}
}
}
else
{
uint8_t v___x_560_; 
v___x_560_ = 0;
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg___boxed(lean_object* v_k_561_, lean_object* v_t_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_561_, v_t_562_);
lean_dec(v_t_562_);
lean_dec(v_k_561_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(lean_object* v___x_565_, lean_object* v_e_566_){
_start:
{
uint8_t v___x_567_; lean_object* v_d_569_; lean_object* v_b_570_; 
v___x_567_ = l_Lean_Expr_hasFVar(v_e_566_);
if (v___x_567_ == 0)
{
return v___x_567_;
}
else
{
switch(lean_obj_tag(v_e_566_))
{
case 7:
{
lean_object* v_binderType_573_; lean_object* v_body_574_; 
v_binderType_573_ = lean_ctor_get(v_e_566_, 1);
v_body_574_ = lean_ctor_get(v_e_566_, 2);
v_d_569_ = v_binderType_573_;
v_b_570_ = v_body_574_;
goto v___jp_568_;
}
case 6:
{
lean_object* v_binderType_575_; lean_object* v_body_576_; 
v_binderType_575_ = lean_ctor_get(v_e_566_, 1);
v_body_576_ = lean_ctor_get(v_e_566_, 2);
v_d_569_ = v_binderType_575_;
v_b_570_ = v_body_576_;
goto v___jp_568_;
}
case 10:
{
lean_object* v_expr_577_; 
v_expr_577_ = lean_ctor_get(v_e_566_, 1);
v_e_566_ = v_expr_577_;
goto _start;
}
case 8:
{
lean_object* v_type_579_; lean_object* v_value_580_; lean_object* v_body_581_; uint8_t v___x_582_; 
v_type_579_ = lean_ctor_get(v_e_566_, 1);
v_value_580_ = lean_ctor_get(v_e_566_, 2);
v_body_581_ = lean_ctor_get(v_e_566_, 3);
v___x_582_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_565_, v_type_579_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; 
v___x_583_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_565_, v_value_580_);
if (v___x_583_ == 0)
{
v_e_566_ = v_body_581_;
goto _start;
}
else
{
return v___x_567_;
}
}
else
{
return v___x_567_;
}
}
case 5:
{
lean_object* v_fn_585_; lean_object* v_arg_586_; uint8_t v___x_587_; 
v_fn_585_ = lean_ctor_get(v_e_566_, 0);
v_arg_586_ = lean_ctor_get(v_e_566_, 1);
v___x_587_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_565_, v_fn_585_);
if (v___x_587_ == 0)
{
v_e_566_ = v_arg_586_;
goto _start;
}
else
{
return v___x_567_;
}
}
case 11:
{
lean_object* v_struct_589_; 
v_struct_589_ = lean_ctor_get(v_e_566_, 2);
v_e_566_ = v_struct_589_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_591_; uint8_t v___x_592_; 
v_fvarId_591_ = lean_ctor_get(v_e_566_, 0);
v___x_592_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_fvarId_591_, v___x_565_);
return v___x_592_;
}
default: 
{
uint8_t v___x_593_; 
v___x_593_ = 0;
return v___x_593_;
}
}
}
v___jp_568_:
{
uint8_t v___x_571_; 
v___x_571_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_565_, v_d_569_);
if (v___x_571_ == 0)
{
v_e_566_ = v_b_570_;
goto _start;
}
else
{
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1___boxed(lean_object* v___x_594_, lean_object* v_e_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_594_, v_e_595_);
lean_dec_ref(v_e_595_);
lean_dec(v___x_594_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(lean_object* v_as_598_, size_t v_sz_599_, size_t v_i_600_, lean_object* v_b_601_){
_start:
{
lean_object* v_a_604_; uint8_t v___x_608_; 
v___x_608_ = lean_usize_dec_lt(v_i_600_, v_sz_599_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_b_601_);
return v___x_609_;
}
else
{
lean_object* v_snd_610_; lean_object* v_fst_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_640_; 
v_snd_610_ = lean_ctor_get(v_b_601_, 1);
v_fst_611_ = lean_ctor_get(v_b_601_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_b_601_);
if (v_isSharedCheck_640_ == 0)
{
v___x_613_ = v_b_601_;
v_isShared_614_ = v_isSharedCheck_640_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_610_);
lean_inc(v_fst_611_);
lean_dec(v_b_601_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_640_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_639_; 
v_fst_615_ = lean_ctor_get(v_snd_610_, 0);
v_snd_616_ = lean_ctor_get(v_snd_610_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_snd_610_);
if (v_isSharedCheck_639_ == 0)
{
v___x_618_ = v_snd_610_;
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_snd_610_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_a_620_; lean_object* v_decl_621_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_a_620_ = lean_array_uget_borrowed(v_as_598_, v_i_600_);
v_decl_621_ = lean_ctor_get(v_a_620_, 0);
v___x_632_ = l_Lean_LocalDecl_type(v_decl_621_);
v___x_633_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_611_, v___x_632_);
lean_dec_ref(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_LocalDecl_value(v_decl_621_, v___x_633_);
v___x_635_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_611_, v___x_634_);
lean_dec_ref(v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_del_object(v___x_618_);
lean_del_object(v___x_613_);
lean_inc(v_a_620_);
v___x_636_ = lean_array_push(v_fst_615_, v_a_620_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_snd_616_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_fst_611_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v_a_604_ = v___x_638_;
goto v___jp_603_;
}
else
{
goto v___jp_622_;
}
}
else
{
goto v___jp_622_;
}
v___jp_622_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
lean_inc(v_a_620_);
v___x_623_ = lean_array_push(v_snd_616_, v_a_620_);
v___x_624_ = l_Lean_LocalDecl_fvarId(v_decl_621_);
v___x_625_ = l_Lean_FVarIdSet_insert(v_fst_611_, v___x_624_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_623_);
v___x_627_ = v___x_618_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_fst_615_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_623_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_627_);
lean_ctor_set(v___x_613_, 0, v___x_625_);
v___x_629_ = v___x_613_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v_a_604_ = v___x_629_;
goto v___jp_603_;
}
}
}
}
}
}
v___jp_603_:
{
size_t v___x_605_; size_t v___x_606_; 
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_600_, v___x_605_);
v_i_600_ = v___x_606_;
v_b_601_ = v_a_604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(lean_object* v_as_641_, lean_object* v_sz_642_, lean_object* v_i_643_, lean_object* v_b_644_, lean_object* v___y_645_){
_start:
{
size_t v_sz_boxed_646_; size_t v_i_boxed_647_; lean_object* v_res_648_; 
v_sz_boxed_646_ = lean_unbox_usize(v_sz_642_);
lean_dec(v_sz_642_);
v_i_boxed_647_ = lean_unbox_usize(v_i_643_);
lean_dec(v_i_643_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_641_, v_sz_boxed_646_, v_i_boxed_647_, v_b_644_);
lean_dec_ref(v_as_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object* v_fvar_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_fvarSet_660_; lean_object* v_fvarSet_661_; lean_object* v___x_662_; lean_object* v_decls_663_; lean_object* v___x_664_; lean_object* v___x_665_; size_t v_sz_666_; size_t v___x_667_; lean_object* v___x_668_; 
v_fvarSet_660_ = lean_box(1);
v_fvarSet_661_ = l_Lean_FVarIdSet_insert(v_fvarSet_660_, v_fvar_651_);
v___x_662_ = lean_st_ref_get(v_a_654_);
v_decls_663_ = lean_ctor_get(v___x_662_, 1);
lean_inc_ref(v_decls_663_);
lean_dec(v___x_662_);
v___x_664_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_fvarSet_661_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v_sz_666_ = lean_array_size(v_decls_663_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_decls_663_, v_sz_666_, v___x_667_, v___x_665_);
lean_dec_ref(v_decls_663_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_691_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_691_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_691_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_691_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_snd_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___x_676_; lean_object* v_givenNames_677_; lean_object* v_valueMap_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_689_; 
v_snd_673_ = lean_ctor_get(v_a_669_, 1);
lean_inc(v_snd_673_);
lean_dec(v_a_669_);
v_fst_674_ = lean_ctor_get(v_snd_673_, 0);
lean_inc(v_fst_674_);
v_snd_675_ = lean_ctor_get(v_snd_673_, 1);
lean_inc(v_snd_675_);
lean_dec(v_snd_673_);
v___x_676_ = lean_st_ref_take(v_a_654_);
v_givenNames_677_ = lean_ctor_get(v___x_676_, 0);
v_valueMap_678_ = lean_ctor_get(v___x_676_, 2);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_676_, 1);
lean_dec(v_unused_690_);
v___x_680_ = v___x_676_;
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_valueMap_678_);
lean_inc(v_givenNames_677_);
lean_dec(v___x_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_fst_674_);
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_givenNames_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_fst_674_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_valueMap_678_);
v___x_683_ = v_reuseFailAlloc_688_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_st_ref_put(v_a_654_, v___x_683_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v_snd_675_);
v___x_686_ = v___x_671_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_snd_675_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_668_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_668_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object* v_fvar_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Meta_ExtractLets_flushDecls(v_fvar_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_709_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object* v_00_u03b2_710_, lean_object* v_k_711_, lean_object* v_t_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_711_, v_t_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object* v_00_u03b2_714_, lean_object* v_k_715_, lean_object* v_t_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(v_00_u03b2_714_, v_k_715_, v_t_716_);
lean_dec(v_t_716_);
lean_dec(v_k_715_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object* v_as_719_, size_t v_sz_720_, size_t v_i_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_719_, v_sz_720_, v_i_721_, v_b_722_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object* v_as_732_, lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
size_t v_sz_boxed_744_; size_t v_i_boxed_745_; lean_object* v_res_746_; 
v_sz_boxed_744_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_745_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_732_, v_sz_boxed_744_, v_i_boxed_745_, v_b_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_as_732_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object* v_x_747_){
_start:
{
lean_object* v_decl_748_; 
v_decl_748_ = lean_ctor_get(v_x_747_, 0);
lean_inc_ref(v_decl_748_);
return v_decl_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object* v_x_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(v_x_749_);
lean_dec_ref(v_x_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object* v_lctx_751_, lean_object* v_x1_752_, lean_object* v_x2_753_){
_start:
{
lean_object* v_decl_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_decl_754_ = lean_ctor_get(v_x2_753_, 0);
v___x_755_ = l_Lean_LocalDecl_fvarId(v_decl_754_);
v___x_756_ = l_Lean_LocalContext_contains(v_lctx_751_, v___x_755_);
lean_dec(v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
v___x_757_ = lean_array_push(v_x1_752_, v_x2_753_);
return v___x_757_;
}
else
{
lean_dec_ref(v_x2_753_);
return v_x1_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object* v_lctx_758_, lean_object* v_x1_759_, lean_object* v_x2_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(v_lctx_758_, v_x1_759_, v_x2_760_);
lean_dec_ref(v_lctx_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_k_784_, lean_object* v_decls_785_, lean_object* v_lctx_786_){
_start:
{
lean_object* v___y_788_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_get_size(v_decls_785_);
v___x_797_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_798_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_799_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_lctx_786_);
lean_dec_ref(v_decls_785_);
v___y_788_ = v___x_797_;
goto v___jp_787_;
}
else
{
lean_object* v___f_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_800_, 0, v_lctx_786_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_796_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_798_, v___f_800_, v_decls_785_, v___x_801_, v___x_802_, v___x_797_);
v___y_788_ = v___x_803_;
goto v___jp_787_;
}
v___jp_787_:
{
lean_object* v___x_789_; size_t v_sz_790_; size_t v___x_791_; lean_object* v_decls_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_789_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_790_ = lean_array_size(v___y_788_);
v___x_791_ = ((size_t)0ULL);
v_decls_792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_789_, v___f_781_, v_sz_790_, v___x_791_, v___y_788_);
v___x_793_ = lean_array_to_list(v_decls_792_);
v___x_794_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_782_, v_inst_783_, v___x_793_, v_k_784_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_decls_808_, lean_object* v_k_809_){
_start:
{
lean_object* v_toBind_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___x_813_; 
v_toBind_810_ = lean_ctor_get(v_inst_805_, 1);
lean_inc(v_toBind_810_);
v___f_811_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_812_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_812_, 0, v___f_811_);
lean_closure_set(v___f_812_, 1, v_inst_806_);
lean_closure_set(v___f_812_, 2, v_inst_805_);
lean_closure_set(v___f_812_, 3, v_k_809_);
lean_closure_set(v___f_812_, 4, v_decls_808_);
v___x_813_ = lean_apply_4(v_toBind_810_, lean_box(0), lean_box(0), v_inst_807_, v___f_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_814_, lean_object* v_00_u03b1_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_decls_819_, lean_object* v_k_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_816_, v_inst_817_, v_inst_818_, v_decls_819_, v_k_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_822_, size_t v_i_823_, size_t v_stop_824_, lean_object* v_b_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = lean_usize_dec_eq(v_i_823_, v_stop_824_);
if (v___x_826_ == 0)
{
size_t v___x_827_; size_t v___x_828_; lean_object* v___x_829_; lean_object* v_decl_830_; uint8_t v_isLet_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_827_ = ((size_t)1ULL);
v___x_828_ = lean_usize_sub(v_i_823_, v___x_827_);
v___x_829_ = lean_array_uget_borrowed(v_as_822_, v___x_828_);
v_decl_830_ = lean_ctor_get(v___x_829_, 0);
v_isLet_831_ = lean_ctor_get_uint8(v___x_829_, sizeof(void*)*1);
v___x_832_ = l_Lean_LocalDecl_userName(v_decl_830_);
v___x_833_ = l_Lean_LocalDecl_type(v_decl_830_);
v___x_834_ = l_Lean_LocalDecl_value(v_decl_830_, v___x_826_);
lean_inc_ref(v_decl_830_);
v___x_835_ = l_Lean_LocalDecl_toExpr(v_decl_830_);
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_mk_empty_array_with_capacity(v___x_836_);
v___x_838_ = lean_array_push(v___x_837_, v___x_835_);
v___x_839_ = lean_expr_abstract(v_b_825_, v___x_838_);
lean_dec_ref(v___x_838_);
lean_dec_ref(v_b_825_);
if (v_isLet_831_ == 0)
{
uint8_t v___x_840_; lean_object* v___x_841_; 
v___x_840_ = 1;
v___x_841_ = l_Lean_Expr_letE___override(v___x_832_, v___x_833_, v___x_834_, v___x_839_, v___x_840_);
v_i_823_ = v___x_828_;
v_b_825_ = v___x_841_;
goto _start;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Expr_letE___override(v___x_832_, v___x_833_, v___x_834_, v___x_839_, v___x_826_);
v_i_823_ = v___x_828_;
v_b_825_ = v___x_843_;
goto _start;
}
}
else
{
return v_b_825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object* v_as_845_, lean_object* v_i_846_, lean_object* v_stop_847_, lean_object* v_b_848_){
_start:
{
size_t v_i_boxed_849_; size_t v_stop_boxed_850_; lean_object* v_res_851_; 
v_i_boxed_849_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_stop_boxed_850_ = lean_unbox_usize(v_stop_847_);
lean_dec(v_stop_847_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_845_, v_i_boxed_849_, v_stop_boxed_850_, v_b_848_);
lean_dec_ref(v_as_845_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object* v_decls_852_, lean_object* v_e_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_854_ = lean_array_get_size(v_decls_852_);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_nat_dec_lt(v___x_855_, v___x_854_);
if (v___x_856_ == 0)
{
return v_e_853_;
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_usize_of_nat(v___x_854_);
v___x_858_ = ((size_t)0ULL);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_852_, v___x_857_, v___x_858_, v_e_853_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object* v_decls_860_, lean_object* v_e_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_860_, v_e_861_);
lean_dec_ref(v_decls_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object* v_fvarId_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_bs_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_865_, v_sz_864_);
if (v___x_867_ == 0)
{
return v_bs_866_;
}
else
{
lean_object* v_v_868_; lean_object* v_decl_869_; lean_object* v___x_870_; lean_object* v_bs_x27_871_; lean_object* v___y_873_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_v_868_ = lean_array_uget(v_bs_866_, v_i_865_);
v_decl_869_ = lean_ctor_get(v_v_868_, 0);
v___x_870_ = lean_unsigned_to_nat(0u);
v_bs_x27_871_ = lean_array_uset(v_bs_866_, v_i_865_, v___x_870_);
v___x_878_ = l_Lean_LocalDecl_fvarId(v_decl_869_);
v___x_879_ = l_Lean_instBEqFVarId_beq(v___x_878_, v_fvarId_863_);
lean_dec(v___x_878_);
if (v___x_879_ == 0)
{
v___y_873_ = v_v_868_;
goto v___jp_872_;
}
else
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_inc_ref(v_decl_869_);
v_isSharedCheck_886_ = !lean_is_exclusive(v_v_868_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_v_868_, 0);
lean_dec(v_unused_887_);
v___x_881_ = v_v_868_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_dec(v_v_868_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_decl_869_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1, v___x_879_);
v___y_873_ = v___x_884_;
goto v___jp_872_;
}
}
}
v___jp_872_:
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_865_, v___x_874_);
v___x_876_ = lean_array_uset(v_bs_x27_871_, v_i_865_, v___y_873_);
v_i_865_ = v___x_875_;
v_bs_866_ = v___x_876_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object* v_fvarId_888_, lean_object* v_sz_889_, lean_object* v_i_890_, lean_object* v_bs_891_){
_start:
{
size_t v_sz_boxed_892_; size_t v_i_boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_889_);
lean_dec(v_sz_889_);
v_i_boxed_893_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_888_, v_sz_boxed_892_, v_i_boxed_893_, v_bs_891_);
lean_dec(v_fvarId_888_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object* v_fvarId_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_givenNames_899_; lean_object* v_decls_900_; lean_object* v_valueMap_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_914_; 
v___x_898_ = lean_st_ref_take(v_a_896_);
v_givenNames_899_ = lean_ctor_get(v___x_898_, 0);
v_decls_900_ = lean_ctor_get(v___x_898_, 1);
v_valueMap_901_ = lean_ctor_get(v___x_898_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_914_ == 0)
{
v___x_903_ = v___x_898_;
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_valueMap_901_);
lean_inc(v_decls_900_);
lean_inc(v_givenNames_899_);
lean_dec(v___x_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_905_ = lean_box(0);
v_sz_906_ = lean_array_size(v_decls_900_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_895_, v_sz_906_, v___x_907_, v_decls_900_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v___x_908_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_givenNames_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_valueMap_901_);
v___x_910_ = v_reuseFailAlloc_913_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_st_ref_put(v_a_896_, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_905_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object* v_fvarId_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_915_, v_a_916_);
lean_dec(v_a_916_);
lean_dec(v_fvarId_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object* v_fvarId_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_919_, v_a_922_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object* v_fvarId_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_fvarId_929_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(size_t v_sz_939_, size_t v_i_940_, lean_object* v_bs_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_940_, v_sz_939_);
if (v___x_942_ == 0)
{
return v_bs_941_;
}
else
{
lean_object* v_v_943_; lean_object* v_decl_944_; lean_object* v___x_945_; lean_object* v_bs_x27_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
v_v_943_ = lean_array_uget_borrowed(v_bs_941_, v_i_940_);
v_decl_944_ = lean_ctor_get(v_v_943_, 0);
lean_inc_ref(v_decl_944_);
v___x_945_ = lean_unsigned_to_nat(0u);
v_bs_x27_946_ = lean_array_uset(v_bs_941_, v_i_940_, v___x_945_);
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_940_, v___x_947_);
v___x_949_ = lean_array_uset(v_bs_x27_946_, v_i_940_, v_decl_944_);
v_i_940_ = v___x_948_;
v_bs_941_ = v___x_949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1___boxed(lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_bs_953_){
_start:
{
size_t v_sz_boxed_954_; size_t v_i_boxed_955_; lean_object* v_res_956_; 
v_sz_boxed_954_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_955_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_boxed_954_, v_i_boxed_955_, v_bs_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(lean_object* v_x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
lean_inc(v___y_960_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
v___x_966_ = lean_apply_8(v_x_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, lean_box(0));
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(v_x_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(lean_object* v_decls_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___f_987_; lean_object* v___x_988_; 
lean_inc(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_987_, 0, v_x_978_);
lean_closure_set(v___f_987_, 1, v___y_979_);
lean_closure_set(v___f_987_, 2, v___y_980_);
lean_closure_set(v___f_987_, 3, v___y_981_);
v___x_988_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_977_, v___f_987_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_988_) == 0)
{
return v___x_988_;
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___boxed(lean_object* v_decls_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_997_, v_x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(lean_object* v___x_1008_, lean_object* v_as_1009_, size_t v_i_1010_, size_t v_stop_1011_, lean_object* v_b_1012_){
_start:
{
lean_object* v___y_1014_; uint8_t v___x_1018_; 
v___x_1018_ = lean_usize_dec_eq(v_i_1010_, v_stop_1011_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v_decl_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1019_ = lean_array_uget_borrowed(v_as_1009_, v_i_1010_);
v_decl_1020_ = lean_ctor_get(v___x_1019_, 0);
v___x_1021_ = l_Lean_LocalDecl_fvarId(v_decl_1020_);
v___x_1022_ = l_Lean_LocalContext_contains(v___x_1008_, v___x_1021_);
lean_dec(v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_inc(v___x_1019_);
v___x_1023_ = lean_array_push(v_b_1012_, v___x_1019_);
v___y_1014_ = v___x_1023_;
goto v___jp_1013_;
}
else
{
v___y_1014_ = v_b_1012_;
goto v___jp_1013_;
}
}
else
{
return v_b_1012_;
}
v___jp_1013_:
{
size_t v___x_1015_; size_t v___x_1016_; 
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_add(v_i_1010_, v___x_1015_);
v_i_1010_ = v___x_1016_;
v_b_1012_ = v___y_1014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(lean_object* v___x_1024_, lean_object* v_as_1025_, lean_object* v_i_1026_, lean_object* v_stop_1027_, lean_object* v_b_1028_){
_start:
{
size_t v_i_boxed_1029_; size_t v_stop_boxed_1030_; lean_object* v_res_1031_; 
v_i_boxed_1029_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_stop_boxed_1030_ = lean_unbox_usize(v_stop_1027_);
lean_dec(v_stop_1027_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_1024_, v_as_1025_, v_i_boxed_1029_, v_stop_boxed_1030_, v_b_1028_);
lean_dec_ref(v_as_1025_);
lean_dec_ref(v___x_1024_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(lean_object* v_decls_1032_, lean_object* v_k_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___y_1043_; lean_object* v_lctx_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_lctx_1049_ = lean_ctor_get(v___y_1037_, 2);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_array_get_size(v_decls_1032_);
v___x_1052_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_1053_ = lean_nat_dec_lt(v___x_1050_, v___x_1051_);
if (v___x_1053_ == 0)
{
v___y_1043_ = v___x_1052_;
goto v___jp_1042_;
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = lean_usize_of_nat(v___x_1051_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1049_, v_decls_1032_, v___x_1054_, v___x_1055_, v___x_1052_);
v___y_1043_ = v___x_1056_;
goto v___jp_1042_;
}
v___jp_1042_:
{
size_t v_sz_1044_; size_t v___x_1045_; lean_object* v_decls_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_sz_1044_ = lean_array_size(v___y_1043_);
v___x_1045_ = ((size_t)0ULL);
v_decls_1046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_1044_, v___x_1045_, v___y_1043_);
v___x_1047_ = lean_array_to_list(v_decls_1046_);
v___x_1048_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v___x_1047_, v_k_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object* v_decls_1057_, lean_object* v_k_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1057_, v_k_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v_decls_1057_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_fvarId_1068_, lean_object* v_as_1069_, lean_object* v_j_1070_){
_start:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = lean_array_get_size(v_as_1069_);
v___x_1072_ = lean_nat_dec_lt(v_j_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec(v_j_1070_);
v___x_1073_ = lean_box(0);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v_decl_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1074_ = lean_array_fget_borrowed(v_as_1069_, v_j_1070_);
v_decl_1075_ = lean_ctor_get(v___x_1074_, 0);
v___x_1076_ = l_Lean_LocalDecl_fvarId(v_decl_1075_);
v___x_1077_ = l_Lean_instBEqFVarId_beq(v___x_1076_, v_fvarId_1068_);
lean_dec(v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_j_1070_, v___x_1078_);
lean_dec(v_j_1070_);
v_j_1070_ = v___x_1079_;
goto _start;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_j_1070_);
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_fvarId_1082_, lean_object* v_as_1083_, lean_object* v_j_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1082_, v_as_1083_, v_j_1084_);
lean_dec_ref(v_as_1083_);
lean_dec(v_fvarId_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1086_, lean_object* v_k_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v_lctx_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_st_ref_get(v_a_1090_);
v_lctx_1097_ = lean_ctor_get(v_a_1091_, 2);
v___x_1098_ = l_Lean_LocalContext_contains(v_lctx_1097_, v_fvarId_1086_);
if (v___x_1098_ == 0)
{
lean_object* v_decls_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_decls_1099_ = lean_ctor_get(v___x_1096_, 1);
lean_inc_ref(v_decls_1099_);
lean_dec(v___x_1096_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1086_, v_decls_1099_, v___x_1100_);
if (lean_obj_tag(v___x_1101_) == 1)
{
lean_object* v_val_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_val_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_val_1102_, v___x_1103_);
lean_dec(v_val_1102_);
v___x_1105_ = l_Array_toSubarray___redArg(v_decls_1099_, v___x_1100_, v___x_1104_);
v___x_1106_ = l_Subarray_copy___redArg(v___x_1105_);
v___x_1107_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_1106_, v_k_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
lean_dec_ref(v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v___x_1101_);
lean_dec_ref(v_decls_1099_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
lean_inc(v_a_1092_);
lean_inc_ref(v_a_1091_);
lean_inc(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
v___x_1108_ = lean_apply_8(v_k_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, lean_box(0));
return v___x_1108_;
}
}
else
{
lean_object* v___x_1109_; 
lean_dec(v___x_1096_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
lean_inc(v_a_1092_);
lean_inc_ref(v_a_1091_);
lean_inc(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
v___x_1109_ = lean_apply_8(v_k_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, lean_box(0));
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1110_, lean_object* v_k_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1110_, v_k_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_fvarId_1110_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1121_, lean_object* v_fvarId_1122_, lean_object* v_k_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1122_, v_k_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1133_, lean_object* v_fvarId_1134_, lean_object* v_k_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1133_, v_fvarId_1134_, v_k_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_fvarId_1134_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object* v_00_u03b1_1145_, lean_object* v_decls_1146_, lean_object* v_x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1146_, v_x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_decls_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_1157_, v_decls_1158_, v_x_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object* v_00_u03b1_1169_, lean_object* v_decls_1170_, lean_object* v_k_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1170_, v_k_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_decls_1182_, lean_object* v_k_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_1181_, v_decls_1182_, v_k_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v_decls_1182_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v___x_1196_; 
v___x_1196_ = l_Lean_Expr_hasMVar(v_e_1193_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_e_1193_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v_mctx_1199_; lean_object* v___x_1200_; lean_object* v_fst_1201_; lean_object* v_snd_1202_; lean_object* v___x_1203_; lean_object* v_cache_1204_; lean_object* v_zetaDeltaFVarIds_1205_; lean_object* v_postponed_1206_; lean_object* v_diag_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1216_; 
v___x_1198_ = lean_st_ref_get(v___y_1194_);
v_mctx_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc_ref(v_mctx_1199_);
lean_dec(v___x_1198_);
v___x_1200_ = l_Lean_instantiateMVarsCore(v_mctx_1199_, v_e_1193_);
v_fst_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_fst_1201_);
v_snd_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_snd_1202_);
lean_dec_ref(v___x_1200_);
v___x_1203_ = lean_st_ref_take(v___y_1194_);
v_cache_1204_ = lean_ctor_get(v___x_1203_, 1);
v_zetaDeltaFVarIds_1205_ = lean_ctor_get(v___x_1203_, 2);
v_postponed_1206_ = lean_ctor_get(v___x_1203_, 3);
v_diag_1207_ = lean_ctor_get(v___x_1203_, 4);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1203_, 0);
lean_dec(v_unused_1217_);
v___x_1209_ = v___x_1203_;
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_diag_1207_);
lean_inc(v_postponed_1206_);
lean_inc(v_zetaDeltaFVarIds_1205_);
lean_inc(v_cache_1204_);
lean_dec(v___x_1203_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v_snd_1202_);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_snd_1202_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_cache_1204_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_zetaDeltaFVarIds_1205_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_postponed_1206_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_diag_1207_);
v___x_1212_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_st_ref_put(v___y_1194_, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_fst_1201_);
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1218_, v___y_1219_);
lean_dec(v___y_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1222_, v___y_1227_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1242_, size_t v_i_1243_, size_t v_stop_1244_, lean_object* v_b_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_a_1255_; uint8_t v___x_1261_; 
v___x_1261_ = lean_usize_dec_eq(v_i_1243_, v_stop_1244_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_array_uget_borrowed(v_as_1242_, v_i_1243_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_box(0);
v_a_1255_ = v___x_1263_;
goto v___jp_1254_;
}
else
{
lean_object* v_val_1264_; uint8_t v___x_1265_; 
v_val_1264_ = lean_ctor_get(v___x_1262_, 0);
v___x_1265_ = l_Lean_LocalDecl_isLet(v_val_1264_, v___x_1261_);
if (v___x_1265_ == 0)
{
goto v___jp_1259_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1264_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_Lean_LocalDecl_value(v_val_1264_, v___x_1261_);
v___x_1268_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1267_, v___y_1250_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v_givenNames_1271_; lean_object* v_decls_1272_; lean_object* v_valueMap_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1284_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = lean_st_ref_take(v___y_1248_);
v_givenNames_1271_ = lean_ctor_get(v___x_1270_, 0);
v_decls_1272_ = lean_ctor_get(v___x_1270_, 1);
v_valueMap_1273_ = lean_ctor_get(v___x_1270_, 2);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1275_ = v___x_1270_;
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_valueMap_1273_);
lean_inc(v_decls_1272_);
lean_inc(v_givenNames_1271_);
lean_dec(v___x_1270_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1277_ = lean_box(0);
v___x_1278_ = l_Lean_LocalDecl_fvarId(v_val_1264_);
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1273_, v_a_1269_, v___x_1278_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 2, v___x_1279_);
v___x_1281_ = v___x_1275_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_givenNames_1271_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_decls_1272_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_st_ref_put(v___y_1248_, v___x_1281_);
v_a_1255_ = v___x_1277_;
goto v___jp_1254_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1268_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1268_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
goto v___jp_1259_;
}
}
}
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_b_1245_);
return v___x_1293_;
}
v___jp_1254_:
{
size_t v___x_1256_; size_t v___x_1257_; 
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_add(v_i_1243_, v___x_1256_);
v_i_1243_ = v___x_1257_;
v_b_1245_ = v_a_1255_;
goto _start;
}
v___jp_1259_:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_box(0);
v_a_1255_ = v___x_1260_;
goto v___jp_1254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1294_, lean_object* v_i_1295_, lean_object* v_stop_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
size_t v_i_boxed_1306_; size_t v_stop_boxed_1307_; lean_object* v_res_1308_; 
v_i_boxed_1306_ = lean_unbox_usize(v_i_1295_);
lean_dec(v_i_1295_);
v_stop_boxed_1307_ = lean_unbox_usize(v_stop_1296_);
lean_dec(v_stop_1296_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1294_, v_i_boxed_1306_, v_stop_boxed_1307_, v_b_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_as_1294_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1309_, size_t v_i_1310_, size_t v_stop_1311_, lean_object* v_b_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_a_1322_; uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_eq(v_i_1310_, v_stop_1311_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_array_uget_borrowed(v_as_1309_, v_i_1310_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_box(0);
v_a_1322_ = v___x_1330_;
goto v___jp_1321_;
}
else
{
lean_object* v_val_1331_; uint8_t v___x_1332_; 
v_val_1331_ = lean_ctor_get(v___x_1329_, 0);
v___x_1332_ = l_Lean_LocalDecl_isLet(v_val_1331_, v___x_1328_);
if (v___x_1332_ == 0)
{
goto v___jp_1326_;
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1331_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = l_Lean_LocalDecl_value(v_val_1331_, v___x_1328_);
v___x_1335_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1334_, v___y_1317_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v_givenNames_1338_; lean_object* v_decls_1339_; lean_object* v_valueMap_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1351_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = lean_st_ref_take(v___y_1315_);
v_givenNames_1338_ = lean_ctor_get(v___x_1337_, 0);
v_decls_1339_ = lean_ctor_get(v___x_1337_, 1);
v_valueMap_1340_ = lean_ctor_get(v___x_1337_, 2);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1342_ = v___x_1337_;
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_valueMap_1340_);
lean_inc(v_decls_1339_);
lean_inc(v_givenNames_1338_);
lean_dec(v___x_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Lean_LocalDecl_fvarId(v_val_1331_);
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1340_, v_a_1336_, v___x_1345_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 2, v___x_1346_);
v___x_1348_ = v___x_1342_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_givenNames_1338_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_decls_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_st_ref_put(v___y_1315_, v___x_1348_);
v_a_1322_ = v___x_1344_;
goto v___jp_1321_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1335_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1335_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
goto v___jp_1326_;
}
}
}
}
else
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_b_1312_);
return v___x_1360_;
}
v___jp_1321_:
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1310_, v___x_1323_);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1309_, v___x_1324_, v_stop_1311_, v_a_1322_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1325_;
}
v___jp_1326_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_box(0);
v_a_1322_ = v___x_1327_;
goto v___jp_1321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1361_, lean_object* v_i_1362_, lean_object* v_stop_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
size_t v_i_boxed_1373_; size_t v_stop_boxed_1374_; lean_object* v_res_1375_; 
v_i_boxed_1373_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_stop_boxed_1374_ = lean_unbox_usize(v_stop_1363_);
lean_dec(v_stop_1363_);
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1361_, v_i_boxed_1373_, v_stop_boxed_1374_, v_b_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec_ref(v_as_1361_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v_cs_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1399_; 
v_cs_1385_ = lean_ctor_get(v_x_1376_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1387_ = v_x_1376_;
v_isShared_1388_ = v_isSharedCheck_1399_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_cs_1385_);
lean_dec(v_x_1376_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1399_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_array_get_size(v_cs_1385_);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_nat_dec_lt(v___x_1389_, v___x_1390_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1394_; 
lean_dec_ref(v_cs_1385_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1391_);
v___x_1394_ = v___x_1387_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1391_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
else
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
lean_del_object(v___x_1387_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = lean_usize_of_nat(v___x_1390_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1385_, v___x_1396_, v___x_1397_, v___x_1391_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec_ref(v_cs_1385_);
return v___x_1398_;
}
}
}
else
{
lean_object* v_vs_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1414_; 
v_vs_1400_ = lean_ctor_get(v_x_1376_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1402_ = v_x_1376_;
v_isShared_1403_ = v_isSharedCheck_1414_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_vs_1400_);
lean_dec(v_x_1376_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1414_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_array_get_size(v_vs_1400_);
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1409_; 
lean_dec_ref(v_vs_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1406_);
v___x_1409_ = v___x_1402_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
lean_del_object(v___x_1402_);
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1405_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1400_, v___x_1411_, v___x_1412_, v___x_1406_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec_ref(v_vs_1400_);
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1415_, size_t v_i_1416_, size_t v_stop_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_eq(v_i_1416_, v_stop_1417_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_array_uget_borrowed(v_as_1415_, v_i_1416_);
lean_inc(v___x_1428_);
v___x_1429_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1428_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; size_t v___x_1431_; size_t v___x_1432_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1416_, v___x_1431_);
v_i_1416_ = v___x_1432_;
v_b_1418_ = v_a_1430_;
goto _start;
}
else
{
return v___x_1429_;
}
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_b_1418_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1435_, lean_object* v_i_1436_, lean_object* v_stop_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
size_t v_i_boxed_1447_; size_t v_stop_boxed_1448_; lean_object* v_res_1449_; 
v_i_boxed_1447_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_stop_boxed_1448_ = lean_unbox_usize(v_stop_1437_);
lean_dec(v_stop_1437_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1435_, v_i_boxed_1447_, v_stop_boxed_1448_, v_b_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v_as_1435_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_root_1469_; lean_object* v_tail_1470_; lean_object* v___x_1471_; 
v_root_1469_ = lean_ctor_get(v_t_1460_, 0);
lean_inc_ref(v_root_1469_);
v_tail_1470_ = lean_ctor_get(v_t_1460_, 1);
lean_inc_ref(v_tail_1470_);
lean_dec_ref(v_t_1460_);
v___x_1471_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1469_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1485_; 
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v___x_1471_, 0);
lean_dec(v_unused_1486_);
v___x_1473_ = v___x_1471_;
v_isShared_1474_ = v_isSharedCheck_1485_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v___x_1471_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1485_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_array_get_size(v_tail_1470_);
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_nat_dec_lt(v___x_1475_, v___x_1476_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1480_; 
lean_dec_ref(v_tail_1470_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1477_);
v___x_1480_ = v___x_1473_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1477_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
else
{
size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
lean_del_object(v___x_1473_);
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1476_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1470_, v___x_1482_, v___x_1483_, v___x_1477_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec_ref(v_tail_1470_);
return v___x_1484_;
}
}
}
else
{
lean_dec_ref(v_tail_1470_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1496_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1498_, size_t v_x_1499_, size_t v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_object* v_cs_1509_; lean_object* v___x_1510_; size_t v___x_1511_; lean_object* v_j_1512_; lean_object* v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v_cs_1509_ = lean_ctor_get(v_x_1498_, 0);
lean_inc_ref(v_cs_1509_);
lean_dec_ref_known(v_x_1498_, 1);
v___x_1510_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1511_ = lean_usize_shift_right(v_x_1499_, v_x_1500_);
v_j_1512_ = lean_usize_to_nat(v___x_1511_);
v___x_1513_ = lean_array_get_borrowed(v___x_1510_, v_cs_1509_, v_j_1512_);
v___x_1514_ = ((size_t)1ULL);
v___x_1515_ = lean_usize_shift_left(v___x_1514_, v_x_1500_);
v___x_1516_ = lean_usize_sub(v___x_1515_, v___x_1514_);
v___x_1517_ = lean_usize_land(v_x_1499_, v___x_1516_);
v___x_1518_ = ((size_t)5ULL);
v___x_1519_ = lean_usize_sub(v_x_1500_, v___x_1518_);
lean_inc(v___x_1513_);
v___x_1520_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1513_, v___x_1517_, v___x_1519_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1535_; 
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1520_, 0);
lean_dec(v_unused_1536_);
v___x_1522_ = v___x_1520_;
v_isShared_1523_ = v_isSharedCheck_1535_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v___x_1520_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1535_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = lean_nat_add(v_j_1512_, v___x_1524_);
lean_dec(v_j_1512_);
v___x_1526_ = lean_array_get_size(v_cs_1509_);
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_nat_dec_lt(v___x_1525_, v___x_1526_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1530_; 
lean_dec(v___x_1525_);
lean_dec_ref(v_cs_1509_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1527_);
v___x_1530_ = v___x_1522_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1527_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
else
{
size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
lean_del_object(v___x_1522_);
v___x_1532_ = lean_usize_of_nat(v___x_1525_);
lean_dec(v___x_1525_);
v___x_1533_ = lean_usize_of_nat(v___x_1526_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1509_, v___x_1532_, v___x_1533_, v___x_1527_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec_ref(v_cs_1509_);
return v___x_1534_;
}
}
}
else
{
lean_dec(v_j_1512_);
lean_dec_ref(v_cs_1509_);
return v___x_1520_;
}
}
else
{
lean_object* v_vs_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1551_; 
v_vs_1537_ = lean_ctor_get(v_x_1498_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_x_1498_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1539_ = v_x_1498_;
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_vs_1537_);
lean_dec(v_x_1498_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1541_ = lean_usize_to_nat(v_x_1499_);
v___x_1542_ = lean_array_get_size(v_vs_1537_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_nat_dec_lt(v___x_1541_, v___x_1542_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1546_; 
lean_dec(v___x_1541_);
lean_dec_ref(v_vs_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1543_);
v___x_1546_ = v___x_1539_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1543_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
lean_del_object(v___x_1539_);
v___x_1548_ = lean_usize_of_nat(v___x_1541_);
lean_dec(v___x_1541_);
v___x_1549_ = lean_usize_of_nat(v___x_1542_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1537_, v___x_1548_, v___x_1549_, v___x_1543_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec_ref(v_vs_1537_);
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
size_t v_x_9267__boxed_1563_; size_t v_x_9268__boxed_1564_; lean_object* v_res_1565_; 
v_x_9267__boxed_1563_ = lean_unbox_usize(v_x_1553_);
lean_dec(v_x_1553_);
v_x_9268__boxed_1564_ = lean_unbox_usize(v_x_1554_);
lean_dec(v_x_1554_);
v_res_1565_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1552_, v_x_9267__boxed_1563_, v_x_9268__boxed_1564_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1566_, lean_object* v_start_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = lean_nat_dec_eq(v_start_1567_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v_root_1578_; lean_object* v_tail_1579_; size_t v_shift_1580_; lean_object* v_tailOff_1581_; uint8_t v___x_1582_; 
v_root_1578_ = lean_ctor_get(v_t_1566_, 0);
lean_inc_ref(v_root_1578_);
v_tail_1579_ = lean_ctor_get(v_t_1566_, 1);
lean_inc_ref(v_tail_1579_);
v_shift_1580_ = lean_ctor_get_usize(v_t_1566_, 4);
v_tailOff_1581_ = lean_ctor_get(v_t_1566_, 3);
lean_inc(v_tailOff_1581_);
lean_dec_ref(v_t_1566_);
v___x_1582_ = lean_nat_dec_le(v_tailOff_1581_, v_start_1567_);
if (v___x_1582_ == 0)
{
size_t v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v_tailOff_1581_);
v___x_1583_ = lean_usize_of_nat(v_start_1567_);
v___x_1584_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1578_, v___x_1583_, v_shift_1580_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v___x_1584_, 0);
lean_dec(v_unused_1598_);
v___x_1586_ = v___x_1584_;
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v___x_1584_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1588_ = lean_array_get_size(v_tail_1579_);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_nat_dec_lt(v___x_1576_, v___x_1588_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1592_; 
lean_dec_ref(v_tail_1579_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1592_ = v___x_1586_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1589_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
else
{
size_t v___x_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
lean_del_object(v___x_1586_);
v___x_1594_ = ((size_t)0ULL);
v___x_1595_ = lean_usize_of_nat(v___x_1588_);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1579_, v___x_1594_, v___x_1595_, v___x_1589_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec_ref(v_tail_1579_);
return v___x_1596_;
}
}
}
else
{
lean_dec_ref(v_tail_1579_);
return v___x_1584_;
}
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
lean_dec_ref(v_root_1578_);
v___x_1599_ = lean_nat_sub(v_start_1567_, v_tailOff_1581_);
lean_dec(v_tailOff_1581_);
v___x_1600_ = lean_array_get_size(v_tail_1579_);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_nat_dec_lt(v___x_1599_, v___x_1600_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_dec(v___x_1599_);
lean_dec_ref(v_tail_1579_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
return v___x_1603_;
}
else
{
size_t v___x_1604_; size_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = lean_usize_of_nat(v___x_1599_);
lean_dec(v___x_1599_);
v___x_1605_ = lean_usize_of_nat(v___x_1600_);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1579_, v___x_1604_, v___x_1605_, v___x_1601_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec_ref(v_tail_1579_);
return v___x_1606_;
}
}
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1566_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1608_, lean_object* v_start_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1608_, v_start_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v_start_1609_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1619_, lean_object* v_start_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_decls_1629_; lean_object* v___x_1630_; 
v_decls_1629_ = lean_ctor_get(v_lctx_1619_, 1);
lean_inc_ref(v_decls_1629_);
lean_dec_ref(v_lctx_1619_);
v___x_1630_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1629_, v_start_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1631_, lean_object* v_start_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1631_, v_start_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v_start_1632_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_lctx_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_lctx_1650_ = lean_ctor_get(v_a_1645_, 2);
v___x_1651_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1650_);
v___x_1652_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1650_, v___x_1651_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
return v_res_1661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1663_){
_start:
{
lean_object* v___f_1664_; lean_object* v___x_1665_; 
v___f_1664_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1665_ = lean_find_expr(v___f_1664_, v_e_1663_);
if (lean_obj_tag(v___x_1665_) == 0)
{
uint8_t v___x_1666_; 
v___x_1666_ = 0;
return v___x_1666_;
}
else
{
uint8_t v___x_1667_; 
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = 1;
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1668_){
_start:
{
uint8_t v_res_1669_; lean_object* v_r_1670_; 
v_res_1669_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1668_);
lean_dec_ref(v_e_1668_);
v_r_1670_ = lean_box(v_res_1669_);
return v_r_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
v___x_1681_ = lean_apply_9(v_k_1671_, v_b_1675_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, lean_box(0));
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v_b_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v_b_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1693_, uint8_t v_bi_1694_, lean_object* v_type_1695_, lean_object* v_k_1696_, uint8_t v_kind_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___f_1706_; lean_object* v___x_1707_; 
lean_inc(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
v___f_1706_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1706_, 0, v_k_1696_);
lean_closure_set(v___f_1706_, 1, v___y_1698_);
lean_closure_set(v___f_1706_, 2, v___y_1699_);
lean_closure_set(v___f_1706_, 3, v___y_1700_);
v___x_1707_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1693_, v_bi_1694_, v_type_1695_, v___f_1706_, v_kind_1697_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
if (lean_obj_tag(v___x_1707_) == 0)
{
return v___x_1707_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1716_, lean_object* v_bi_1717_, lean_object* v_type_1718_, lean_object* v_k_1719_, lean_object* v_kind_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v_bi_boxed_1729_; uint8_t v_kind_boxed_1730_; lean_object* v_res_1731_; 
v_bi_boxed_1729_ = lean_unbox(v_bi_1717_);
v_kind_boxed_1730_ = lean_unbox(v_kind_1720_);
v_res_1731_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1716_, v_bi_boxed_1729_, v_type_1718_, v_k_1719_, v_kind_boxed_1730_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1732_, lean_object* v_name_1733_, uint8_t v_bi_1734_, lean_object* v_type_1735_, lean_object* v_k_1736_, uint8_t v_kind_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1733_, v_bi_1734_, v_type_1735_, v_k_1736_, v_kind_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_name_1748_, lean_object* v_bi_1749_, lean_object* v_type_1750_, lean_object* v_k_1751_, lean_object* v_kind_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
uint8_t v_bi_boxed_1761_; uint8_t v_kind_boxed_1762_; lean_object* v_res_1763_; 
v_bi_boxed_1761_ = lean_unbox(v_bi_1749_);
v_kind_boxed_1762_ = lean_unbox(v_kind_1752_);
v_res_1763_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1747_, v_name_1748_, v_bi_boxed_1761_, v_type_1750_, v_k_1751_, v_kind_boxed_1762_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1764_, lean_object* v_e_1765_, lean_object* v___f_1766_, lean_object* v_____r_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
if (v_types_1764_ == 0)
{
lean_object* v___x_1776_; 
lean_inc_ref(v_e_1765_);
v___x_1776_ = l_Lean_Meta_isType(v_e_1765_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1787_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_unbox(v_a_1777_);
lean_dec(v_a_1777_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_del_object(v___x_1779_);
lean_dec_ref(v_e_1765_);
v___x_1782_ = lean_box(0);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1773_);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc(v___y_1769_);
lean_inc_ref(v___y_1768_);
v___x_1783_ = lean_apply_9(v___f_1766_, v___x_1782_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, lean_box(0));
return v___x_1783_;
}
else
{
lean_object* v___x_1785_; 
lean_dec_ref(v___f_1766_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v_e_1765_);
v___x_1785_ = v___x_1779_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_e_1765_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v___f_1766_);
lean_dec_ref(v_e_1765_);
v_a_1788_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1776_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1776_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref(v_e_1765_);
v___x_1796_ = lean_box(0);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1773_);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
lean_inc(v___y_1770_);
lean_inc(v___y_1769_);
lean_inc_ref(v___y_1768_);
v___x_1797_ = lean_apply_9(v___f_1766_, v___x_1796_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, lean_box(0));
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1798_, lean_object* v_e_1799_, lean_object* v___f_1800_, lean_object* v_____r_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v_types_boxed_1810_; lean_object* v_res_1811_; 
v_types_boxed_1810_ = lean_unbox(v_types_1798_);
v_res_1811_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1810_, v_e_1799_, v___f_1800_, v_____r_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1811_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1812_, uint8_t v___y_1813_){
_start:
{
if (v___y_1813_ == 0)
{
if (v___y_1812_ == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = 1;
return v___x_1814_;
}
else
{
return v___y_1813_;
}
}
else
{
return v___y_1812_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v___y_41877__boxed_1817_; uint8_t v___y_41878__boxed_1818_; uint8_t v_res_1819_; lean_object* v_r_1820_; 
v___y_41877__boxed_1817_ = lean_unbox(v___y_1815_);
v___y_41878__boxed_1818_ = lean_unbox(v___y_1816_);
v_res_1819_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_41877__boxed_1817_, v___y_41878__boxed_1818_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_instMonadEIO___redArg();
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_toApplicative_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1912_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1840_ = l_StateRefT_x27_instMonad___redArg(v___x_1839_);
v_toApplicative_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v___x_1840_, 1);
lean_dec(v_unused_1913_);
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1912_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_toApplicative_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1912_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_toFunctor_1845_; lean_object* v_toSeq_1846_; lean_object* v_toSeqLeft_1847_; lean_object* v_toSeqRight_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1910_; 
v_toFunctor_1845_ = lean_ctor_get(v_toApplicative_1841_, 0);
v_toSeq_1846_ = lean_ctor_get(v_toApplicative_1841_, 2);
v_toSeqLeft_1847_ = lean_ctor_get(v_toApplicative_1841_, 3);
v_toSeqRight_1848_ = lean_ctor_get(v_toApplicative_1841_, 4);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_toApplicative_1841_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v_toApplicative_1841_, 1);
lean_dec(v_unused_1911_);
v___x_1850_ = v_toApplicative_1841_;
v_isShared_1851_ = v_isSharedCheck_1910_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_toSeqRight_1848_);
lean_inc(v_toSeqLeft_1847_);
lean_inc(v_toSeq_1846_);
lean_inc(v_toFunctor_1845_);
lean_dec(v_toApplicative_1841_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1910_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___f_1855_; lean_object* v___x_1856_; lean_object* v___f_1857_; lean_object* v___f_1858_; lean_object* v___f_1859_; lean_object* v___x_1861_; 
v___f_1852_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1853_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1845_);
v___f_1854_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1854_, 0, v_toFunctor_1845_);
v___f_1855_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1855_, 0, v_toFunctor_1845_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___f_1854_);
lean_ctor_set(v___x_1856_, 1, v___f_1855_);
v___f_1857_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1857_, 0, v_toSeqRight_1848_);
v___f_1858_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1858_, 0, v_toSeqLeft_1847_);
v___f_1859_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1859_, 0, v_toSeq_1846_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 4, v___f_1857_);
lean_ctor_set(v___x_1850_, 3, v___f_1858_);
lean_ctor_set(v___x_1850_, 2, v___f_1859_);
lean_ctor_set(v___x_1850_, 1, v___f_1852_);
lean_ctor_set(v___x_1850_, 0, v___x_1856_);
v___x_1861_ = v___x_1850_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___f_1852_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v___f_1859_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v___f_1858_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v___f_1857_);
v___x_1861_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___f_1853_);
lean_ctor_set(v___x_1843_, 0, v___x_1861_);
v___x_1863_ = v___x_1843_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___f_1853_);
v___x_1863_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v_toApplicative_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1906_; 
v___x_1864_ = l_StateRefT_x27_instMonad___redArg(v___x_1863_);
v_toApplicative_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; 
v_unused_1907_ = lean_ctor_get(v___x_1864_, 1);
lean_dec(v_unused_1907_);
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1906_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_toApplicative_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1906_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_toFunctor_1869_; lean_object* v_toSeq_1870_; lean_object* v_toSeqLeft_1871_; lean_object* v_toSeqRight_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1904_; 
v_toFunctor_1869_ = lean_ctor_get(v_toApplicative_1865_, 0);
v_toSeq_1870_ = lean_ctor_get(v_toApplicative_1865_, 2);
v_toSeqLeft_1871_ = lean_ctor_get(v_toApplicative_1865_, 3);
v_toSeqRight_1872_ = lean_ctor_get(v_toApplicative_1865_, 4);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_toApplicative_1865_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; 
v_unused_1905_ = lean_ctor_get(v_toApplicative_1865_, 1);
lean_dec(v_unused_1905_);
v___x_1874_ = v_toApplicative_1865_;
v_isShared_1875_ = v_isSharedCheck_1904_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_toSeqRight_1872_);
lean_inc(v_toSeqLeft_1871_);
lean_inc(v_toSeq_1870_);
lean_inc(v_toFunctor_1869_);
lean_dec(v_toApplicative_1865_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1904_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___f_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___f_1882_; lean_object* v___f_1883_; lean_object* v___f_1884_; lean_object* v___f_1885_; lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___f_1888_; lean_object* v___f_1889_; lean_object* v___f_1890_; lean_object* v___x_1892_; 
v___f_1876_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1877_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1877_, 0, v___f_1876_);
v___x_1878_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1879_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1879_, 0, v___f_1877_);
lean_closure_set(v___f_1879_, 1, v___x_1878_);
v___f_1880_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1881_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1882_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1882_, 0, v___f_1880_);
lean_closure_set(v___f_1882_, 1, v___x_1881_);
v___f_1883_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1884_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1869_);
v___f_1885_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1885_, 0, v_toFunctor_1869_);
v___f_1886_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1886_, 0, v_toFunctor_1869_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___f_1885_);
lean_ctor_set(v___x_1887_, 1, v___f_1886_);
v___f_1888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1888_, 0, v_toSeqRight_1872_);
v___f_1889_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1889_, 0, v_toSeqLeft_1871_);
v___f_1890_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1890_, 0, v_toSeq_1870_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 4, v___f_1888_);
lean_ctor_set(v___x_1874_, 3, v___f_1889_);
lean_ctor_set(v___x_1874_, 2, v___f_1890_);
lean_ctor_set(v___x_1874_, 1, v___f_1883_);
lean_ctor_set(v___x_1874_, 0, v___x_1887_);
v___x_1892_ = v___x_1874_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___f_1883_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v___f_1890_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v___f_1889_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v___f_1888_);
v___x_1892_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v___f_1884_);
lean_ctor_set(v___x_1867_, 0, v___x_1892_);
v___x_1894_ = v___x_1867_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___f_1884_);
v___x_1894_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_38719__overap_1900_; lean_object* v___x_1901_; 
v___x_1895_ = l_StateRefT_x27_instMonad___redArg(v___x_1894_);
v___x_1896_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1838_, v___f_1879_, v___f_1882_, v___x_1895_);
v___x_1897_ = l_Lean_instInhabitedExpr;
v___x_1898_ = l_instInhabitedOfMonad___redArg(v___x_1896_, v___x_1897_);
v___f_1899_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1899_, 0, v___x_1898_);
v___x_38719__overap_1900_ = lean_panic_fn_borrowed(v___f_1899_, v_msg_1829_);
lean_dec_ref(v___f_1899_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___x_1901_ = lean_apply_8(v___x_38719__overap_1900_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, lean_box(0));
return v___x_1901_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderType_1924_, lean_object* v_binderName_1925_, uint8_t v_binderInfo_1926_, lean_object* v_body_1927_, lean_object* v_e_1928_, lean_object* v_t_1929_, lean_object* v_b_1930_){
_start:
{
size_t v___x_1931_; size_t v___x_1932_; uint8_t v___x_1933_; 
v___x_1931_ = lean_ptr_addr(v_binderType_1924_);
v___x_1932_ = lean_ptr_addr(v_t_1929_);
v___x_1933_ = lean_usize_dec_eq(v___x_1931_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Expr_lam___override(v_binderName_1925_, v_t_1929_, v_b_1930_, v_binderInfo_1926_);
return v___x_1934_;
}
else
{
size_t v___x_1935_; size_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_ptr_addr(v_body_1927_);
v___x_1936_ = lean_ptr_addr(v_b_1930_);
v___x_1937_ = lean_usize_dec_eq(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_Expr_lam___override(v_binderName_1925_, v_t_1929_, v_b_1930_, v_binderInfo_1926_);
return v___x_1938_;
}
else
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1926_, v_binderInfo_1926_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_Expr_lam___override(v_binderName_1925_, v_t_1929_, v_b_1930_, v_binderInfo_1926_);
return v___x_1940_;
}
else
{
lean_dec_ref(v_b_1930_);
lean_dec_ref(v_t_1929_);
lean_dec(v_binderName_1925_);
lean_inc_ref(v_e_1928_);
return v_e_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderType_1941_, lean_object* v_binderName_1942_, lean_object* v_binderInfo_1943_, lean_object* v_body_1944_, lean_object* v_e_1945_, lean_object* v_t_1946_, lean_object* v_b_1947_){
_start:
{
uint8_t v_binderInfo_42065__boxed_1948_; lean_object* v_res_1949_; 
v_binderInfo_42065__boxed_1948_ = lean_unbox(v_binderInfo_1943_);
v_res_1949_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderType_1941_, v_binderName_1942_, v_binderInfo_42065__boxed_1948_, v_body_1944_, v_e_1945_, v_t_1946_, v_b_1947_);
lean_dec_ref(v_e_1945_);
lean_dec_ref(v_body_1944_);
lean_dec_ref(v_binderType_1941_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderType_1950_, lean_object* v_binderName_1951_, uint8_t v_binderInfo_1952_, lean_object* v_body_1953_, lean_object* v_e_1954_, lean_object* v_t_1955_, lean_object* v_b_1956_){
_start:
{
size_t v___x_1957_; size_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = lean_ptr_addr(v_binderType_1950_);
v___x_1958_ = lean_ptr_addr(v_t_1955_);
v___x_1959_ = lean_usize_dec_eq(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_Expr_forallE___override(v_binderName_1951_, v_t_1955_, v_b_1956_, v_binderInfo_1952_);
return v___x_1960_;
}
else
{
size_t v___x_1961_; size_t v___x_1962_; uint8_t v___x_1963_; 
v___x_1961_ = lean_ptr_addr(v_body_1953_);
v___x_1962_ = lean_ptr_addr(v_b_1956_);
v___x_1963_ = lean_usize_dec_eq(v___x_1961_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Expr_forallE___override(v_binderName_1951_, v_t_1955_, v_b_1956_, v_binderInfo_1952_);
return v___x_1964_;
}
else
{
uint8_t v___x_1965_; 
v___x_1965_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1952_, v_binderInfo_1952_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Expr_forallE___override(v_binderName_1951_, v_t_1955_, v_b_1956_, v_binderInfo_1952_);
return v___x_1966_;
}
else
{
lean_dec_ref(v_b_1956_);
lean_dec_ref(v_t_1955_);
lean_dec(v_binderName_1951_);
lean_inc_ref(v_e_1954_);
return v_e_1954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderType_1967_, lean_object* v_binderName_1968_, lean_object* v_binderInfo_1969_, lean_object* v_body_1970_, lean_object* v_e_1971_, lean_object* v_t_1972_, lean_object* v_b_1973_){
_start:
{
uint8_t v_binderInfo_42097__boxed_1974_; lean_object* v_res_1975_; 
v_binderInfo_42097__boxed_1974_ = lean_unbox(v_binderInfo_1969_);
v_res_1975_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderType_1967_, v_binderName_1968_, v_binderInfo_42097__boxed_1974_, v_body_1970_, v_e_1971_, v_t_1972_, v_b_1973_);
lean_dec_ref(v_e_1971_);
lean_dec_ref(v_body_1970_);
lean_dec_ref(v_binderType_1967_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_1976_, lean_object* v_type_1977_, lean_object* v_val_1978_, lean_object* v_k_1979_, uint8_t v_nondep_1980_, uint8_t v_kind_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___f_1990_; lean_object* v___x_1991_; 
lean_inc(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
v___f_1990_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1990_, 0, v_k_1979_);
lean_closure_set(v___f_1990_, 1, v___y_1982_);
lean_closure_set(v___f_1990_, 2, v___y_1983_);
lean_closure_set(v___f_1990_, 3, v___y_1984_);
v___x_1991_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1976_, v_type_1977_, v_val_1978_, v___f_1990_, v_nondep_1980_, v_kind_1981_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_1991_) == 0)
{
return v___x_1991_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2000_, lean_object* v_type_2001_, lean_object* v_val_2002_, lean_object* v_k_2003_, lean_object* v_nondep_2004_, lean_object* v_kind_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v_nondep_boxed_2014_; uint8_t v_kind_boxed_2015_; lean_object* v_res_2016_; 
v_nondep_boxed_2014_ = lean_unbox(v_nondep_2004_);
v_kind_boxed_2015_ = lean_unbox(v_kind_2005_);
v_res_2016_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2000_, v_type_2001_, v_val_2002_, v_k_2003_, v_nondep_boxed_2014_, v_kind_boxed_2015_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = l_Lean_instInhabitedExpr;
v___x_2019_ = lean_panic_fn_borrowed(v___x_2018_, v_msg_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2020_, lean_object* v_x_2021_){
_start:
{
if (lean_obj_tag(v_x_2021_) == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_box(0);
return v___x_2022_;
}
else
{
lean_object* v_key_2023_; lean_object* v_value_2024_; lean_object* v_tail_2025_; uint8_t v___x_2026_; 
v_key_2023_ = lean_ctor_get(v_x_2021_, 0);
v_value_2024_ = lean_ctor_get(v_x_2021_, 1);
v_tail_2025_ = lean_ctor_get(v_x_2021_, 2);
v___x_2026_ = l_Lean_ExprStructEq_beq(v_key_2023_, v_a_2020_);
if (v___x_2026_ == 0)
{
v_x_2021_ = v_tail_2025_;
goto _start;
}
else
{
lean_object* v___x_2028_; 
lean_inc(v_value_2024_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v_value_2024_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2029_, v_x_2030_);
lean_dec(v_x_2030_);
lean_dec_ref(v_a_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v_buckets_2034_; lean_object* v___x_2035_; uint64_t v___x_2036_; uint64_t v___x_2037_; uint64_t v___x_2038_; uint64_t v_fold_2039_; uint64_t v___x_2040_; uint64_t v___x_2041_; uint64_t v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; size_t v___x_2046_; size_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_buckets_2034_ = lean_ctor_get(v_m_2032_, 1);
v___x_2035_ = lean_array_get_size(v_buckets_2034_);
v___x_2036_ = l_Lean_ExprStructEq_hash(v_a_2033_);
v___x_2037_ = 32ULL;
v___x_2038_ = lean_uint64_shift_right(v___x_2036_, v___x_2037_);
v_fold_2039_ = lean_uint64_xor(v___x_2036_, v___x_2038_);
v___x_2040_ = 16ULL;
v___x_2041_ = lean_uint64_shift_right(v_fold_2039_, v___x_2040_);
v___x_2042_ = lean_uint64_xor(v_fold_2039_, v___x_2041_);
v___x_2043_ = lean_uint64_to_usize(v___x_2042_);
v___x_2044_ = lean_usize_of_nat(v___x_2035_);
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_sub(v___x_2044_, v___x_2045_);
v___x_2047_ = lean_usize_land(v___x_2043_, v___x_2046_);
v___x_2048_ = lean_array_uget_borrowed(v_buckets_2034_, v___x_2047_);
v___x_2049_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2033_, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2050_, v_a_2051_);
lean_dec_ref(v_a_2051_);
lean_dec_ref(v_m_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2053_, lean_object* v_x_2054_){
_start:
{
if (lean_obj_tag(v_x_2054_) == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = 0;
return v___x_2055_;
}
else
{
lean_object* v_key_2056_; lean_object* v_tail_2057_; lean_object* v_fst_2058_; lean_object* v_snd_2059_; lean_object* v_fst_2060_; lean_object* v_snd_2061_; uint8_t v___x_2065_; 
v_key_2056_ = lean_ctor_get(v_x_2054_, 0);
v_tail_2057_ = lean_ctor_get(v_x_2054_, 2);
v_fst_2058_ = lean_ctor_get(v_key_2056_, 0);
v_snd_2059_ = lean_ctor_get(v_key_2056_, 1);
v_fst_2060_ = lean_ctor_get(v_a_2053_, 0);
v_snd_2061_ = lean_ctor_get(v_a_2053_, 1);
v___x_2065_ = lean_unbox(v_fst_2060_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_unbox(v_fst_2058_);
if (v___x_2066_ == 0)
{
goto v___jp_2062_;
}
else
{
v_x_2054_ = v_tail_2057_;
goto _start;
}
}
else
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_unbox(v_fst_2058_);
if (v___x_2068_ == 0)
{
v_x_2054_ = v_tail_2057_;
goto _start;
}
else
{
goto v___jp_2062_;
}
}
v___jp_2062_:
{
uint8_t v___x_2063_; 
v___x_2063_ = l_Lean_ExprStructEq_beq(v_snd_2059_, v_snd_2061_);
if (v___x_2063_ == 0)
{
v_x_2054_ = v_tail_2057_;
goto _start;
}
else
{
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2070_, lean_object* v_x_2071_){
_start:
{
uint8_t v_res_2072_; lean_object* v_r_2073_; 
v_res_2072_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2070_, v_x_2071_);
lean_dec(v_x_2071_);
lean_dec_ref(v_a_2070_);
v_r_2073_ = lean_box(v_res_2072_);
return v_r_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2074_, lean_object* v_b_2075_, lean_object* v_x_2076_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
lean_dec(v_b_2075_);
lean_dec_ref(v_a_2074_);
return v_x_2076_;
}
else
{
lean_object* v_key_2077_; lean_object* v_value_2078_; lean_object* v_tail_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2098_; 
v_key_2077_ = lean_ctor_get(v_x_2076_, 0);
v_value_2078_ = lean_ctor_get(v_x_2076_, 1);
v_tail_2079_ = lean_ctor_get(v_x_2076_, 2);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_x_2076_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2081_ = v_x_2076_;
v_isShared_2082_ = v_isSharedCheck_2098_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_tail_2079_);
lean_inc(v_value_2078_);
lean_inc(v_key_2077_);
lean_dec(v_x_2076_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2098_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v_fst_2090_; lean_object* v_snd_2091_; uint8_t v___x_2095_; 
v_fst_2088_ = lean_ctor_get(v_key_2077_, 0);
v_snd_2089_ = lean_ctor_get(v_key_2077_, 1);
v_fst_2090_ = lean_ctor_get(v_a_2074_, 0);
v_snd_2091_ = lean_ctor_get(v_a_2074_, 1);
v___x_2095_ = lean_unbox(v_fst_2090_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_unbox(v_fst_2088_);
if (v___x_2096_ == 0)
{
goto v___jp_2092_;
}
else
{
goto v___jp_2083_;
}
}
else
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_unbox(v_fst_2088_);
if (v___x_2097_ == 0)
{
goto v___jp_2083_;
}
else
{
goto v___jp_2092_;
}
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2074_, v_b_2075_, v_tail_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 2, v___x_2084_);
v___x_2086_ = v___x_2081_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_key_2077_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_value_2078_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
v___jp_2092_:
{
uint8_t v___x_2093_; 
v___x_2093_ = l_Lean_ExprStructEq_beq(v_snd_2089_, v_snd_2091_);
if (v___x_2093_ == 0)
{
goto v___jp_2083_;
}
else
{
lean_object* v___x_2094_; 
lean_del_object(v___x_2081_);
lean_dec(v_value_2078_);
lean_dec(v_key_2077_);
v___x_2094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2094_, 0, v_a_2074_);
lean_ctor_set(v___x_2094_, 1, v_b_2075_);
lean_ctor_set(v___x_2094_, 2, v_tail_2079_);
return v___x_2094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
return v_x_2099_;
}
else
{
lean_object* v_key_2101_; lean_object* v_value_2102_; lean_object* v_tail_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2134_; 
v_key_2101_ = lean_ctor_get(v_x_2100_, 0);
v_value_2102_ = lean_ctor_get(v_x_2100_, 1);
v_tail_2103_ = lean_ctor_get(v_x_2100_, 2);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2105_ = v_x_2100_;
v_isShared_2106_ = v_isSharedCheck_2134_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_tail_2103_);
lean_inc(v_value_2102_);
lean_inc(v_key_2101_);
lean_dec(v_x_2100_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2134_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_fst_2107_; lean_object* v_snd_2108_; lean_object* v___x_2109_; uint64_t v___y_2111_; uint8_t v___x_2131_; 
v_fst_2107_ = lean_ctor_get(v_key_2101_, 0);
v_snd_2108_ = lean_ctor_get(v_key_2101_, 1);
v___x_2109_ = lean_array_get_size(v_x_2099_);
v___x_2131_ = lean_unbox(v_fst_2107_);
if (v___x_2131_ == 0)
{
uint64_t v___x_2132_; 
v___x_2132_ = 13ULL;
v___y_2111_ = v___x_2132_;
goto v___jp_2110_;
}
else
{
uint64_t v___x_2133_; 
v___x_2133_ = 11ULL;
v___y_2111_ = v___x_2133_;
goto v___jp_2110_;
}
v___jp_2110_:
{
uint64_t v___x_2112_; uint64_t v___x_2113_; uint64_t v___x_2114_; uint64_t v___x_2115_; uint64_t v_fold_2116_; uint64_t v___x_2117_; uint64_t v___x_2118_; uint64_t v___x_2119_; size_t v___x_2120_; size_t v___x_2121_; size_t v___x_2122_; size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2112_ = l_Lean_ExprStructEq_hash(v_snd_2108_);
v___x_2113_ = lean_uint64_mix_hash(v___y_2111_, v___x_2112_);
v___x_2114_ = 32ULL;
v___x_2115_ = lean_uint64_shift_right(v___x_2113_, v___x_2114_);
v_fold_2116_ = lean_uint64_xor(v___x_2113_, v___x_2115_);
v___x_2117_ = 16ULL;
v___x_2118_ = lean_uint64_shift_right(v_fold_2116_, v___x_2117_);
v___x_2119_ = lean_uint64_xor(v_fold_2116_, v___x_2118_);
v___x_2120_ = lean_uint64_to_usize(v___x_2119_);
v___x_2121_ = lean_usize_of_nat(v___x_2109_);
v___x_2122_ = ((size_t)1ULL);
v___x_2123_ = lean_usize_sub(v___x_2121_, v___x_2122_);
v___x_2124_ = lean_usize_land(v___x_2120_, v___x_2123_);
v___x_2125_ = lean_array_uget_borrowed(v_x_2099_, v___x_2124_);
lean_inc(v___x_2125_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 2, v___x_2125_);
v___x_2127_ = v___x_2105_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_key_2101_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_value_2102_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_array_uset(v_x_2099_, v___x_2124_, v___x_2127_);
v_x_2099_ = v___x_2128_;
v_x_2100_ = v_tail_2103_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2135_, lean_object* v_source_2136_, lean_object* v_target_2137_){
_start:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_array_get_size(v_source_2136_);
v___x_2139_ = lean_nat_dec_lt(v_i_2135_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_dec_ref(v_source_2136_);
lean_dec(v_i_2135_);
return v_target_2137_;
}
else
{
lean_object* v_es_2140_; lean_object* v___x_2141_; lean_object* v_source_2142_; lean_object* v_target_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_es_2140_ = lean_array_fget(v_source_2136_, v_i_2135_);
v___x_2141_ = lean_box(0);
v_source_2142_ = lean_array_fset(v_source_2136_, v_i_2135_, v___x_2141_);
v_target_2143_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2137_, v_es_2140_);
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = lean_nat_add(v_i_2135_, v___x_2144_);
lean_dec(v_i_2135_);
v_i_2135_ = v___x_2145_;
v_source_2136_ = v_source_2142_;
v_target_2137_ = v_target_2143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_nbuckets_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2148_ = lean_array_get_size(v_data_2147_);
v___x_2149_ = lean_unsigned_to_nat(2u);
v_nbuckets_2150_ = lean_nat_mul(v___x_2148_, v___x_2149_);
v___x_2151_ = lean_unsigned_to_nat(0u);
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_mk_array(v_nbuckets_2150_, v___x_2152_);
v___x_2154_ = lean_array_propagate_mark(v_data_2147_, v___x_2153_);
v___x_2155_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2151_, v_data_2147_, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2156_, lean_object* v_a_2157_, lean_object* v_b_2158_){
_start:
{
lean_object* v_size_2159_; lean_object* v_buckets_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2211_; 
v_size_2159_ = lean_ctor_get(v_m_2156_, 0);
v_buckets_2160_ = lean_ctor_get(v_m_2156_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_m_2156_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2162_ = v_m_2156_;
v_isShared_2163_ = v_isSharedCheck_2211_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_buckets_2160_);
lean_inc(v_size_2159_);
lean_dec(v_m_2156_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2211_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_fst_2164_; lean_object* v_snd_2165_; lean_object* v___x_2166_; uint64_t v___y_2168_; uint8_t v___x_2208_; 
v_fst_2164_ = lean_ctor_get(v_a_2157_, 0);
v_snd_2165_ = lean_ctor_get(v_a_2157_, 1);
v___x_2166_ = lean_array_get_size(v_buckets_2160_);
v___x_2208_ = lean_unbox(v_fst_2164_);
if (v___x_2208_ == 0)
{
uint64_t v___x_2209_; 
v___x_2209_ = 13ULL;
v___y_2168_ = v___x_2209_;
goto v___jp_2167_;
}
else
{
uint64_t v___x_2210_; 
v___x_2210_ = 11ULL;
v___y_2168_ = v___x_2210_;
goto v___jp_2167_;
}
v___jp_2167_:
{
uint64_t v___x_2169_; uint64_t v___x_2170_; uint64_t v___x_2171_; uint64_t v___x_2172_; uint64_t v_fold_2173_; uint64_t v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; lean_object* v_bkt_2182_; uint8_t v___x_2183_; 
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
v_bkt_2182_ = lean_array_uget_borrowed(v_buckets_2160_, v___x_2181_);
v___x_2183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2157_, v_bkt_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v_size_x27_2185_; lean_object* v___x_2186_; lean_object* v_buckets_x27_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2184_ = lean_unsigned_to_nat(1u);
v_size_x27_2185_ = lean_nat_add(v_size_2159_, v___x_2184_);
lean_dec(v_size_2159_);
lean_inc(v_bkt_2182_);
v___x_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2157_);
lean_ctor_set(v___x_2186_, 1, v_b_2158_);
lean_ctor_set(v___x_2186_, 2, v_bkt_2182_);
v_buckets_x27_2187_ = lean_array_uset(v_buckets_2160_, v___x_2181_, v___x_2186_);
v___x_2188_ = lean_unsigned_to_nat(4u);
v___x_2189_ = lean_nat_mul(v_size_x27_2185_, v___x_2188_);
v___x_2190_ = lean_unsigned_to_nat(3u);
v___x_2191_ = lean_nat_div(v___x_2189_, v___x_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_array_get_size(v_buckets_x27_2187_);
v___x_2193_ = lean_nat_dec_le(v___x_2191_, v___x_2192_);
lean_dec(v___x_2191_);
if (v___x_2193_ == 0)
{
lean_object* v_val_2194_; lean_object* v___x_2196_; 
v_val_2194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2187_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v_val_2194_);
lean_ctor_set(v___x_2162_, 0, v_size_x27_2185_);
v___x_2196_ = v___x_2162_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_size_x27_2185_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_val_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
lean_object* v___x_2199_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v_buckets_x27_2187_);
lean_ctor_set(v___x_2162_, 0, v_size_x27_2185_);
v___x_2199_ = v___x_2162_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_size_x27_2185_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_buckets_x27_2187_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v_buckets_x27_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_inc(v_bkt_2182_);
v___x_2201_ = lean_box(0);
v_buckets_x27_2202_ = lean_array_uset(v_buckets_2160_, v___x_2181_, v___x_2201_);
v___x_2203_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2157_, v_b_2158_, v_bkt_2182_);
v___x_2204_ = lean_array_uset(v_buckets_x27_2202_, v___x_2181_, v___x_2203_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v___x_2204_);
v___x_2206_ = v___x_2162_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_size_2159_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2212_, lean_object* v_x_2213_){
_start:
{
if (lean_obj_tag(v_x_2213_) == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_box(0);
return v___x_2214_;
}
else
{
lean_object* v_key_2215_; lean_object* v_value_2216_; lean_object* v_tail_2217_; lean_object* v_fst_2218_; lean_object* v_snd_2219_; lean_object* v_fst_2220_; lean_object* v_snd_2221_; uint8_t v___x_2226_; 
v_key_2215_ = lean_ctor_get(v_x_2213_, 0);
v_value_2216_ = lean_ctor_get(v_x_2213_, 1);
v_tail_2217_ = lean_ctor_get(v_x_2213_, 2);
v_fst_2218_ = lean_ctor_get(v_key_2215_, 0);
v_snd_2219_ = lean_ctor_get(v_key_2215_, 1);
v_fst_2220_ = lean_ctor_get(v_a_2212_, 0);
v_snd_2221_ = lean_ctor_get(v_a_2212_, 1);
v___x_2226_ = lean_unbox(v_fst_2220_);
if (v___x_2226_ == 0)
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_unbox(v_fst_2218_);
if (v___x_2227_ == 0)
{
goto v___jp_2222_;
}
else
{
v_x_2213_ = v_tail_2217_;
goto _start;
}
}
else
{
uint8_t v___x_2229_; 
v___x_2229_ = lean_unbox(v_fst_2218_);
if (v___x_2229_ == 0)
{
v_x_2213_ = v_tail_2217_;
goto _start;
}
else
{
goto v___jp_2222_;
}
}
v___jp_2222_:
{
uint8_t v___x_2223_; 
v___x_2223_ = l_Lean_ExprStructEq_beq(v_snd_2219_, v_snd_2221_);
if (v___x_2223_ == 0)
{
v_x_2213_ = v_tail_2217_;
goto _start;
}
else
{
lean_object* v___x_2225_; 
lean_inc(v_value_2216_);
v___x_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_value_2216_);
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2231_, v_x_2232_);
lean_dec(v_x_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_buckets_2236_; lean_object* v_fst_2237_; lean_object* v_snd_2238_; lean_object* v___x_2239_; uint64_t v___y_2241_; uint8_t v___x_2257_; 
v_buckets_2236_ = lean_ctor_get(v_m_2234_, 1);
v_fst_2237_ = lean_ctor_get(v_a_2235_, 0);
v_snd_2238_ = lean_ctor_get(v_a_2235_, 1);
v___x_2239_ = lean_array_get_size(v_buckets_2236_);
v___x_2257_ = lean_unbox(v_fst_2237_);
if (v___x_2257_ == 0)
{
uint64_t v___x_2258_; 
v___x_2258_ = 13ULL;
v___y_2241_ = v___x_2258_;
goto v___jp_2240_;
}
else
{
uint64_t v___x_2259_; 
v___x_2259_ = 11ULL;
v___y_2241_ = v___x_2259_;
goto v___jp_2240_;
}
v___jp_2240_:
{
uint64_t v___x_2242_; uint64_t v___x_2243_; uint64_t v___x_2244_; uint64_t v___x_2245_; uint64_t v_fold_2246_; uint64_t v___x_2247_; uint64_t v___x_2248_; uint64_t v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; size_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2242_ = l_Lean_ExprStructEq_hash(v_snd_2238_);
v___x_2243_ = lean_uint64_mix_hash(v___y_2241_, v___x_2242_);
v___x_2244_ = 32ULL;
v___x_2245_ = lean_uint64_shift_right(v___x_2243_, v___x_2244_);
v_fold_2246_ = lean_uint64_xor(v___x_2243_, v___x_2245_);
v___x_2247_ = 16ULL;
v___x_2248_ = lean_uint64_shift_right(v_fold_2246_, v___x_2247_);
v___x_2249_ = lean_uint64_xor(v_fold_2246_, v___x_2248_);
v___x_2250_ = lean_uint64_to_usize(v___x_2249_);
v___x_2251_ = lean_usize_of_nat(v___x_2239_);
v___x_2252_ = ((size_t)1ULL);
v___x_2253_ = lean_usize_sub(v___x_2251_, v___x_2252_);
v___x_2254_ = lean_usize_land(v___x_2250_, v___x_2253_);
v___x_2255_ = lean_array_uget_borrowed(v_buckets_2236_, v___x_2254_);
v___x_2256_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2235_, v___x_2255_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2260_, v_a_2261_);
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_m_2260_);
return v_res_2262_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2263_; lean_object* v_dummy_2264_; 
v___x_2263_ = lean_box(0);
v_dummy_2264_ = l_Lean_Expr_sort___override(v___x_2263_);
return v_dummy_2264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2265_, lean_object* v_fst_2266_, lean_object* v_fvars_2267_, lean_object* v_a_2268_, lean_object* v_b_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_a_2279_; uint8_t v___x_2283_; 
v___x_2283_ = lean_nat_dec_lt(v_a_2268_, v_upperBound_2265_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec(v_a_2268_);
lean_dec(v_fvars_2267_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_b_2269_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v_binderInfo_2287_; uint8_t v___x_2288_; 
v___x_2285_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2286_ = lean_array_get_borrowed(v___x_2285_, v_fst_2266_, v_a_2268_);
v_binderInfo_2287_ = lean_ctor_get_uint8(v___x_2286_, sizeof(void*)*2);
v___x_2288_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2287_);
if (v___x_2288_ == 0)
{
v_a_2279_ = v_b_2269_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = l_Lean_instInhabitedExpr;
v___x_2290_ = 0;
v___x_2291_ = lean_array_get_borrowed(v___x_2289_, v_b_2269_, v_a_2268_);
lean_inc(v___x_2291_);
lean_inc(v_fvars_2267_);
v___x_2292_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2267_, v___x_2291_, v___x_2290_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = lean_array_set(v_b_2269_, v_a_2268_, v_a_2293_);
v_a_2279_ = v___x_2294_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v_b_2269_);
lean_dec(v_a_2268_);
lean_dec(v_fvars_2267_);
v_a_2295_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2292_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2292_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
v___jp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_nat_add(v_a_2268_, v___x_2280_);
lean_dec(v_a_2268_);
v_a_2268_ = v___x_2281_;
v_b_2269_ = v_a_2279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2303_, size_t v_sz_2304_, size_t v_i_2305_, lean_object* v_bs_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = lean_usize_dec_lt(v_i_2305_, v_sz_2304_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
lean_dec(v_fvars_2303_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_bs_2306_);
return v___x_2316_;
}
else
{
uint8_t v___x_2317_; lean_object* v_v_2318_; lean_object* v___x_2319_; lean_object* v_bs_x27_2320_; lean_object* v___x_2321_; 
v___x_2317_ = 0;
v_v_2318_ = lean_array_uget(v_bs_2306_, v_i_2305_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v_bs_x27_2320_ = lean_array_uset(v_bs_2306_, v_i_2305_, v___x_2319_);
lean_inc(v_fvars_2303_);
v___x_2321_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2303_, v_v_2318_, v___x_2317_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2305_, v___x_2323_);
v___x_2325_ = lean_array_uset(v_bs_x27_2320_, v_i_2305_, v_a_2322_);
v_i_2305_ = v___x_2324_;
v_bs_2306_ = v___x_2325_;
goto _start;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v_bs_x27_2320_);
lean_dec(v_fvars_2303_);
v_a_2327_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2321_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2321_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2335_, lean_object* v_f_2336_, lean_object* v_args_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = 0;
lean_inc_ref(v_f_2336_);
lean_inc(v_fvars_2335_);
v___x_2347_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2335_, v_f_2336_, v___x_2346_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2347_) == 0)
{
uint8_t v_implicits_2348_; 
v_implicits_2348_ = lean_ctor_get_uint8(v_a_2338_, 2);
if (v_implicits_2348_ == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2347_, 1);
lean_inc(v_a_2344_);
lean_inc_ref(v_a_2343_);
lean_inc(v_a_2342_);
lean_inc_ref(v_a_2341_);
v___x_2350_ = lean_infer_type(v_f_2336_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2352_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2351_, v_args_2337_, v___x_2346_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v_fst_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v_fst_2354_ = lean_ctor_get(v_a_2353_, 0);
lean_inc(v_fst_2354_);
lean_dec(v_a_2353_);
v___x_2355_ = lean_array_get_size(v_args_2337_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2355_, v_fst_2354_, v_fvars_2335_, v___x_2356_, v_args_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_fst_2354_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2366_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = l_Lean_mkAppN(v_a_2349_, v_a_2358_);
lean_dec(v_a_2358_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2362_);
v___x_2364_ = v___x_2360_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_a_2349_);
v_a_2367_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2357_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2357_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_a_2349_);
lean_dec_ref(v_args_2337_);
lean_dec(v_fvars_2335_);
v_a_2375_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2352_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2352_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_dec(v_a_2349_);
lean_dec_ref(v_args_2337_);
lean_dec(v_fvars_2335_);
return v___x_2350_;
}
}
else
{
lean_object* v_a_2383_; size_t v_sz_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_f_2336_);
v_a_2383_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2347_, 1);
v_sz_2384_ = lean_array_size(v_args_2337_);
v___x_2385_ = ((size_t)0ULL);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2335_, v_sz_2384_, v___x_2385_, v_args_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2395_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = l_Lean_mkAppN(v_a_2383_, v_a_2387_);
lean_dec(v_a_2387_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2391_);
v___x_2393_ = v___x_2389_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_a_2383_);
v_a_2396_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2386_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2386_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2337_);
lean_dec_ref(v_f_2336_);
lean_dec(v_fvars_2335_);
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2404_, lean_object* v_f_2405_, lean_object* v_args_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2404_, v_f_2405_, v_args_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2416_, lean_object* v_b_2417_, uint8_t v___x_2418_, lean_object* v_mk_2419_, lean_object* v_a_2420_, lean_object* v_x_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_inc_ref(v_x_2421_);
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_x_2421_);
lean_ctor_set(v___x_2430_, 1, v_fvars_2416_);
v___x_2431_ = lean_expr_instantiate1(v_b_2417_, v_x_2421_);
v___x_2432_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2430_, v___x_2431_, v___x_2418_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2432_) == 0)
{
uint8_t v_lift_2433_; 
v_lift_2433_ = lean_ctor_get_uint8(v___y_2422_, 10);
if (v_lift_2433_ == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2446_; 
v_a_2434_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2436_ = v___x_2432_;
v_isShared_2437_ = v_isSharedCheck_2446_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2432_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2446_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = lean_mk_empty_array_with_capacity(v___x_2438_);
v___x_2440_ = lean_array_push(v___x_2439_, v_x_2421_);
v___x_2441_ = lean_expr_abstract(v_a_2434_, v___x_2440_);
lean_dec_ref(v___x_2440_);
lean_dec(v_a_2434_);
v___x_2442_ = lean_apply_2(v_mk_2419_, v_a_2420_, v___x_2441_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2442_);
v___x_2444_ = v___x_2436_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_a_2447_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2448_ = l_Lean_Expr_fvarId_x21(v_x_2421_);
v___x_2449_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2448_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2463_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2463_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2463_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2454_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2450_, v_a_2447_);
lean_dec(v_a_2450_);
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lean_mk_empty_array_with_capacity(v___x_2455_);
v___x_2457_ = lean_array_push(v___x_2456_, v_x_2421_);
v___x_2458_ = lean_expr_abstract(v___x_2454_, v___x_2457_);
lean_dec_ref(v___x_2457_);
lean_dec_ref(v___x_2454_);
v___x_2459_ = lean_apply_2(v_mk_2419_, v_a_2420_, v___x_2458_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2459_);
v___x_2461_ = v___x_2452_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_a_2447_);
lean_dec_ref(v_x_2421_);
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_mk_2419_);
v_a_2464_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2449_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2449_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2421_);
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_mk_2419_);
return v___x_2432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2472_, lean_object* v_b_2473_, lean_object* v___x_2474_, lean_object* v_mk_2475_, lean_object* v_a_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v___x_42686__boxed_2486_; lean_object* v_res_2487_; 
v___x_42686__boxed_2486_ = lean_unbox(v___x_2474_);
v_res_2487_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2472_, v_b_2473_, v___x_42686__boxed_2486_, v_mk_2475_, v_a_2476_, v_x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v_b_2473_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2488_, lean_object* v_n_2489_, lean_object* v_t_2490_, lean_object* v_b_2491_, uint8_t v_i_2492_, lean_object* v_mk_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
uint8_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = 0;
lean_inc(v_fvars_2488_);
v___x_2503_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2488_, v_t_2490_, v___x_2502_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
if (lean_obj_tag(v___x_2503_) == 0)
{
uint8_t v_underBinder_2504_; 
v_underBinder_2504_ = lean_ctor_get_uint8(v_a_2494_, 4);
if (v_underBinder_2504_ == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_n_2489_);
lean_dec(v_fvars_2488_);
v_a_2505_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2507_ = v___x_2503_;
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2503_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_apply_2(v_mk_2493_, v_a_2505_, v_b_2491_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2509_);
v___x_2511_ = v___x_2507_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; 
v_a_2514_ = lean_ctor_get(v___x_2503_, 0);
lean_inc_n(v_a_2514_, 2);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2515_ = lean_box(v___x_2502_);
v___f_2516_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2516_, 0, v_fvars_2488_);
lean_closure_set(v___f_2516_, 1, v_b_2491_);
lean_closure_set(v___f_2516_, 2, v___x_2515_);
lean_closure_set(v___f_2516_, 3, v_mk_2493_);
lean_closure_set(v___f_2516_, 4, v_a_2514_);
v___x_2517_ = 0;
v___x_2518_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2489_, v_i_2492_, v_a_2514_, v___f_2516_, v___x_2517_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2518_;
}
}
else
{
lean_dec_ref(v_mk_2493_);
lean_dec_ref(v_b_2491_);
lean_dec(v_n_2489_);
lean_dec(v_fvars_2488_);
return v___x_2503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2519_, lean_object* v_n_2520_, lean_object* v_t_2521_, lean_object* v_b_2522_, lean_object* v_i_2523_, lean_object* v_mk_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
uint8_t v_i_boxed_2533_; lean_object* v_res_2534_; 
v_i_boxed_2533_ = lean_unbox(v_i_2523_);
v_res_2534_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2519_, v_n_2520_, v_t_2521_, v_b_2522_, v_i_boxed_2533_, v_mk_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2535_, lean_object* v_e_2536_, lean_object* v_topLevel_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_topLevel_boxed_2546_; lean_object* v_res_2547_; 
v_topLevel_boxed_2546_ = lean_unbox(v_topLevel_2537_);
v_res_2547_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2535_, v_e_2536_, v_topLevel_boxed_2546_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2552_ = lean_unsigned_to_nat(27u);
v___x_2553_ = lean_unsigned_to_nat(1981u);
v___x_2554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2556_ = l_mkPanicMessageWithDecl(v___x_2555_, v___x_2554_, v___x_2553_, v___x_2552_, v___x_2551_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2557_, lean_object* v_fvars_2558_, lean_object* v_b_2559_, uint8_t v___x_2560_, lean_object* v_e_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, uint8_t v_isLet_2564_, uint8_t v_topLevel_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
if (v_fst_2557_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_inc_ref(v_x_2566_);
v___x_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_x_2566_);
lean_ctor_set(v___x_2575_, 1, v_fvars_2558_);
v___x_2576_ = lean_expr_instantiate1(v_b_2559_, v_x_2566_);
v___x_2577_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2575_, v___x_2576_, v___x_2560_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2577_) == 0)
{
if (lean_obj_tag(v_e_2561_) == 8)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2615_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2615_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2615_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_declName_2582_; lean_object* v_type_2583_; lean_object* v_value_2584_; lean_object* v_body_2585_; uint8_t v_nondep_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; size_t v___x_2591_; size_t v___x_2592_; uint8_t v___x_2593_; 
v_declName_2582_ = lean_ctor_get(v_e_2561_, 0);
v_type_2583_ = lean_ctor_get(v_e_2561_, 1);
v_value_2584_ = lean_ctor_get(v_e_2561_, 2);
v_body_2585_ = lean_ctor_get(v_e_2561_, 3);
v_nondep_2586_ = lean_ctor_get_uint8(v_e_2561_, sizeof(void*)*4 + 8);
v___x_2587_ = lean_unsigned_to_nat(1u);
v___x_2588_ = lean_mk_empty_array_with_capacity(v___x_2587_);
v___x_2589_ = lean_array_push(v___x_2588_, v_x_2566_);
v___x_2590_ = lean_expr_abstract(v_a_2578_, v___x_2589_);
lean_dec_ref(v___x_2589_);
lean_dec(v_a_2578_);
v___x_2591_ = lean_ptr_addr(v_type_2583_);
v___x_2592_ = lean_ptr_addr(v_a_2562_);
v___x_2593_ = lean_usize_dec_eq(v___x_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_inc(v_declName_2582_);
lean_dec_ref_known(v_e_2561_, 4);
v___x_2594_ = l_Lean_Expr_letE___override(v_declName_2582_, v_a_2562_, v_a_2563_, v___x_2590_, v_nondep_2586_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2594_);
v___x_2596_ = v___x_2580_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
else
{
size_t v___x_2598_; size_t v___x_2599_; uint8_t v___x_2600_; 
v___x_2598_ = lean_ptr_addr(v_value_2584_);
v___x_2599_ = lean_ptr_addr(v_a_2563_);
v___x_2600_ = lean_usize_dec_eq(v___x_2598_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
lean_inc(v_declName_2582_);
lean_dec_ref_known(v_e_2561_, 4);
v___x_2601_ = l_Lean_Expr_letE___override(v_declName_2582_, v_a_2562_, v_a_2563_, v___x_2590_, v_nondep_2586_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2601_);
v___x_2603_ = v___x_2580_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
size_t v___x_2605_; size_t v___x_2606_; uint8_t v___x_2607_; 
v___x_2605_ = lean_ptr_addr(v_body_2585_);
v___x_2606_ = lean_ptr_addr(v___x_2590_);
v___x_2607_ = lean_usize_dec_eq(v___x_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_inc(v_declName_2582_);
lean_dec_ref_known(v_e_2561_, 4);
v___x_2608_ = l_Lean_Expr_letE___override(v_declName_2582_, v_a_2562_, v_a_2563_, v___x_2590_, v_nondep_2586_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2608_);
v___x_2610_ = v___x_2580_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
else
{
lean_object* v___x_2613_; 
lean_dec_ref(v___x_2590_);
lean_dec_ref(v_a_2563_);
lean_dec_ref(v_a_2562_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v_e_2561_);
v___x_2613_ = v___x_2580_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_e_2561_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
else
{
lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_x_2566_);
lean_dec_ref(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec_ref(v_e_2561_);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v___x_2577_, 0);
lean_dec(v_unused_2625_);
v___x_2617_ = v___x_2577_;
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
else
{
lean_dec(v___x_2577_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2620_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2619_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2620_);
v___x_2622_ = v___x_2617_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_dec_ref(v_x_2566_);
lean_dec_ref(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec_ref(v_e_2561_);
return v___x_2577_;
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec_ref(v_e_2561_);
v___x_2626_ = l_Lean_Expr_fvarId_x21(v_x_2566_);
v___x_2627_ = l_Lean_FVarId_getDecl___redArg(v___x_2626_, v___y_2570_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2628_, v_isLet_2564_, v___y_2567_, v___y_2569_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec_ref_known(v___x_2629_, 1);
v___x_2630_ = lean_expr_instantiate1(v_b_2559_, v_x_2566_);
lean_dec_ref(v_x_2566_);
v___x_2631_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2558_, v___x_2630_, v_topLevel_2565_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2631_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_x_2566_);
lean_dec(v_fvars_2558_);
v_a_2632_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2629_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2629_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec_ref(v_x_2566_);
lean_dec(v_fvars_2558_);
v_a_2640_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2627_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2627_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2648_ = _args[0];
lean_object* v_fvars_2649_ = _args[1];
lean_object* v_b_2650_ = _args[2];
lean_object* v___x_2651_ = _args[3];
lean_object* v_e_2652_ = _args[4];
lean_object* v_a_2653_ = _args[5];
lean_object* v_a_2654_ = _args[6];
lean_object* v_isLet_2655_ = _args[7];
lean_object* v_topLevel_2656_ = _args[8];
lean_object* v_x_2657_ = _args[9];
lean_object* v___y_2658_ = _args[10];
lean_object* v___y_2659_ = _args[11];
lean_object* v___y_2660_ = _args[12];
lean_object* v___y_2661_ = _args[13];
lean_object* v___y_2662_ = _args[14];
lean_object* v___y_2663_ = _args[15];
lean_object* v___y_2664_ = _args[16];
lean_object* v___y_2665_ = _args[17];
_start:
{
uint8_t v_fst_42831__boxed_2666_; uint8_t v___x_42832__boxed_2667_; uint8_t v_isLet_boxed_2668_; uint8_t v_topLevel_boxed_2669_; lean_object* v_res_2670_; 
v_fst_42831__boxed_2666_ = lean_unbox(v_fst_2648_);
v___x_42832__boxed_2667_ = lean_unbox(v___x_2651_);
v_isLet_boxed_2668_ = lean_unbox(v_isLet_2655_);
v_topLevel_boxed_2669_ = lean_unbox(v_topLevel_2656_);
v_res_2670_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_42831__boxed_2666_, v_fvars_2649_, v_b_2650_, v___x_42832__boxed_2667_, v_e_2652_, v_a_2653_, v_a_2654_, v_isLet_boxed_2668_, v_topLevel_boxed_2669_, v_x_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec_ref(v_b_2650_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2671_, lean_object* v_e_2672_, uint8_t v_isLet_2673_, lean_object* v_n_2674_, lean_object* v_t_2675_, lean_object* v_v_2676_, lean_object* v_b_2677_, uint8_t v_topLevel_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = 0;
lean_inc(v_fvars_2671_);
v___x_2702_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2671_, v_t_2675_, v___x_2701_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
lean_inc(v_fvars_2671_);
v___x_2704_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2671_, v_v_2676_, v___x_2701_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2816_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2816_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2816_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; uint8_t v_descend_2756_; uint8_t v_underBinder_2757_; uint8_t v_usedOnly_2758_; uint8_t v_merge_2759_; uint8_t v_lift_2760_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; uint8_t v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2798_; 
v_descend_2756_ = lean_ctor_get_uint8(v_a_2679_, 3);
v_underBinder_2757_ = lean_ctor_get_uint8(v_a_2679_, 4);
v_usedOnly_2758_ = lean_ctor_get_uint8(v_a_2679_, 5);
v_merge_2759_ = lean_ctor_get_uint8(v_a_2679_, 6);
v_lift_2760_ = lean_ctor_get_uint8(v_a_2679_, 10);
if (v_usedOnly_2758_ == 0)
{
v___y_2798_ = v___x_2701_;
goto v___jp_2797_;
}
else
{
uint8_t v___x_2814_; 
v___x_2814_ = l_Lean_Expr_hasLooseBVars(v_b_2677_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; 
lean_del_object(v___x_2707_);
lean_dec(v_a_2705_);
lean_dec(v_a_2703_);
lean_dec(v_n_2674_);
lean_dec_ref(v_e_2672_);
v___x_2815_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2671_, v_b_2677_, v_topLevel_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
return v___x_2815_;
}
else
{
v___y_2798_ = v___x_2701_;
goto v___jp_2797_;
}
}
v___jp_2709_:
{
if (lean_obj_tag(v_e_2672_) == 8)
{
lean_object* v_declName_2710_; lean_object* v_type_2711_; lean_object* v_value_2712_; lean_object* v_body_2713_; uint8_t v_nondep_2714_; size_t v___x_2715_; size_t v___x_2716_; uint8_t v___x_2717_; 
v_declName_2710_ = lean_ctor_get(v_e_2672_, 0);
v_type_2711_ = lean_ctor_get(v_e_2672_, 1);
v_value_2712_ = lean_ctor_get(v_e_2672_, 2);
v_body_2713_ = lean_ctor_get(v_e_2672_, 3);
v_nondep_2714_ = lean_ctor_get_uint8(v_e_2672_, sizeof(void*)*4 + 8);
v___x_2715_ = lean_ptr_addr(v_type_2711_);
v___x_2716_ = lean_ptr_addr(v_a_2703_);
v___x_2717_ = lean_usize_dec_eq(v___x_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_inc(v_declName_2710_);
lean_dec_ref_known(v_e_2672_, 4);
v___x_2718_ = l_Lean_Expr_letE___override(v_declName_2710_, v_a_2703_, v_a_2705_, v_b_2677_, v_nondep_2714_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2718_);
v___x_2720_ = v___x_2707_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
else
{
size_t v___x_2722_; size_t v___x_2723_; uint8_t v___x_2724_; 
v___x_2722_ = lean_ptr_addr(v_value_2712_);
v___x_2723_ = lean_ptr_addr(v_a_2705_);
v___x_2724_ = lean_usize_dec_eq(v___x_2722_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_inc(v_declName_2710_);
lean_dec_ref_known(v_e_2672_, 4);
v___x_2725_ = l_Lean_Expr_letE___override(v_declName_2710_, v_a_2703_, v_a_2705_, v_b_2677_, v_nondep_2714_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2725_);
v___x_2727_ = v___x_2707_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
else
{
size_t v___x_2729_; size_t v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = lean_ptr_addr(v_body_2713_);
v___x_2730_ = lean_ptr_addr(v_b_2677_);
v___x_2731_ = lean_usize_dec_eq(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
lean_inc(v_declName_2710_);
lean_dec_ref_known(v_e_2672_, 4);
v___x_2732_ = l_Lean_Expr_letE___override(v_declName_2710_, v_a_2703_, v_a_2705_, v_b_2677_, v_nondep_2714_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2732_);
v___x_2734_ = v___x_2707_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
else
{
lean_object* v___x_2737_; 
lean_dec(v_a_2705_);
lean_dec(v_a_2703_);
lean_dec_ref(v_b_2677_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v_e_2672_);
v___x_2737_ = v___x_2707_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_e_2672_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
lean_dec(v_a_2705_);
lean_dec(v_a_2703_);
lean_dec_ref(v_b_2677_);
lean_dec_ref(v_e_2672_);
v___x_2739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2740_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2739_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2740_);
v___x_2742_ = v___x_2707_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
v___jp_2744_:
{
uint8_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = 0;
v___x_2755_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2753_, v_a_2703_, v_a_2705_, v___y_2749_, v___x_2701_, v___x_2754_, v___y_2752_, v___y_2751_, v___y_2747_, v___y_2746_, v___y_2745_, v___y_2748_, v___y_2750_);
return v___x_2755_;
}
v___jp_2761_:
{
if (v_underBinder_2757_ == 0)
{
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2766_);
goto v___jp_2709_;
}
else
{
if (v_descend_2756_ == 0)
{
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2766_);
goto v___jp_2709_;
}
else
{
lean_del_object(v___x_2707_);
lean_dec_ref(v_b_2677_);
lean_dec_ref(v_e_2672_);
v___y_2745_ = v___y_2763_;
v___y_2746_ = v___y_2762_;
v___y_2747_ = v___y_2764_;
v___y_2748_ = v___y_2765_;
v___y_2749_ = v___y_2766_;
v___y_2750_ = v___y_2767_;
v___y_2751_ = v___y_2768_;
v___y_2752_ = v___y_2769_;
v___y_2753_ = v___y_2770_;
goto v___jp_2744_;
}
}
}
v___jp_2771_:
{
lean_object* v___x_2780_; 
lean_inc(v_a_2705_);
lean_inc(v_a_2703_);
v___x_2780_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2671_, v_n_2674_, v_a_2703_, v_a_2705_, v___y_2773_, v___y_2775_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v_fst_2782_; lean_object* v_snd_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___f_2787_; uint8_t v___x_2788_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v_fst_2782_ = lean_ctor_get(v_a_2781_, 0);
lean_inc_n(v_fst_2782_, 2);
v_snd_2783_ = lean_ctor_get(v_a_2781_, 1);
lean_inc(v_snd_2783_);
lean_dec(v_a_2781_);
v___x_2784_ = lean_box(v___x_2701_);
v___x_2785_ = lean_box(v_isLet_2673_);
v___x_2786_ = lean_box(v_topLevel_2678_);
lean_inc(v_a_2705_);
lean_inc(v_a_2703_);
lean_inc_ref(v_e_2672_);
lean_inc_ref(v_b_2677_);
v___f_2787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2787_, 0, v_fst_2782_);
lean_closure_set(v___f_2787_, 1, v_fvars_2671_);
lean_closure_set(v___f_2787_, 2, v_b_2677_);
lean_closure_set(v___f_2787_, 3, v___x_2784_);
lean_closure_set(v___f_2787_, 4, v_e_2672_);
lean_closure_set(v___f_2787_, 5, v_a_2703_);
lean_closure_set(v___f_2787_, 6, v_a_2705_);
lean_closure_set(v___f_2787_, 7, v___x_2785_);
lean_closure_set(v___f_2787_, 8, v___x_2786_);
v___x_2788_ = lean_unbox(v_fst_2782_);
lean_dec(v_fst_2782_);
if (v___x_2788_ == 0)
{
v___y_2762_ = v___y_2776_;
v___y_2763_ = v___y_2777_;
v___y_2764_ = v___y_2775_;
v___y_2765_ = v___y_2778_;
v___y_2766_ = v___f_2787_;
v___y_2767_ = v___y_2779_;
v___y_2768_ = v___y_2774_;
v___y_2769_ = v___y_2773_;
v___y_2770_ = v_snd_2783_;
goto v___jp_2761_;
}
else
{
if (v___y_2772_ == 0)
{
lean_del_object(v___x_2707_);
lean_dec_ref(v_b_2677_);
lean_dec_ref(v_e_2672_);
v___y_2745_ = v___y_2777_;
v___y_2746_ = v___y_2776_;
v___y_2747_ = v___y_2775_;
v___y_2748_ = v___y_2778_;
v___y_2749_ = v___f_2787_;
v___y_2750_ = v___y_2779_;
v___y_2751_ = v___y_2774_;
v___y_2752_ = v___y_2773_;
v___y_2753_ = v_snd_2783_;
goto v___jp_2744_;
}
else
{
v___y_2762_ = v___y_2776_;
v___y_2763_ = v___y_2777_;
v___y_2764_ = v___y_2775_;
v___y_2765_ = v___y_2778_;
v___y_2766_ = v___f_2787_;
v___y_2767_ = v___y_2779_;
v___y_2768_ = v___y_2774_;
v___y_2769_ = v___y_2773_;
v___y_2770_ = v_snd_2783_;
goto v___jp_2761_;
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_del_object(v___x_2707_);
lean_dec(v_a_2705_);
lean_dec(v_a_2703_);
lean_dec_ref(v_b_2677_);
lean_dec_ref(v_e_2672_);
lean_dec(v_fvars_2671_);
v_a_2789_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2780_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2780_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
v___jp_2797_:
{
if (v_merge_2759_ == 0)
{
v___y_2772_ = v___y_2798_;
v___y_2773_ = v_a_2679_;
v___y_2774_ = v_a_2680_;
v___y_2775_ = v_a_2681_;
v___y_2776_ = v_a_2682_;
v___y_2777_ = v_a_2683_;
v___y_2778_ = v_a_2684_;
v___y_2779_ = v_a_2685_;
goto v___jp_2771_;
}
else
{
lean_object* v___x_2799_; lean_object* v_valueMap_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_st_ref_get(v_a_2681_);
v_valueMap_2800_ = lean_ctor_get(v___x_2799_, 2);
lean_inc_ref(v_valueMap_2800_);
lean_dec(v___x_2799_);
v___x_2801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2800_, v_a_2705_);
lean_dec_ref(v_valueMap_2800_);
if (lean_obj_tag(v___x_2801_) == 1)
{
lean_del_object(v___x_2707_);
lean_dec(v_a_2705_);
lean_dec(v_a_2703_);
lean_dec(v_n_2674_);
lean_dec_ref(v_e_2672_);
if (v_isLet_2673_ == 0)
{
lean_object* v_val_2802_; 
v_val_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_val_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2688_ = v_val_2802_;
v___y_2689_ = v_a_2679_;
v___y_2690_ = v_a_2680_;
v___y_2691_ = v_a_2681_;
v___y_2692_ = v_a_2682_;
v___y_2693_ = v_a_2683_;
v___y_2694_ = v_a_2684_;
v___y_2695_ = v_a_2685_;
goto v___jp_2687_;
}
else
{
if (v_lift_2760_ == 0)
{
lean_object* v_val_2803_; 
v_val_2803_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2688_ = v_val_2803_;
v___y_2689_ = v_a_2679_;
v___y_2690_ = v_a_2680_;
v___y_2691_ = v_a_2681_;
v___y_2692_ = v_a_2682_;
v___y_2693_ = v_a_2683_;
v___y_2694_ = v_a_2684_;
v___y_2695_ = v_a_2685_;
goto v___jp_2687_;
}
else
{
lean_object* v_val_2804_; lean_object* v___x_2805_; 
v_val_2804_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2805_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2804_, v_a_2681_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_dec_ref_known(v___x_2805_, 1);
v___y_2688_ = v_val_2804_;
v___y_2689_ = v_a_2679_;
v___y_2690_ = v_a_2680_;
v___y_2691_ = v_a_2681_;
v___y_2692_ = v_a_2682_;
v___y_2693_ = v_a_2683_;
v___y_2694_ = v_a_2684_;
v___y_2695_ = v_a_2685_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec(v_val_2804_);
lean_dec_ref(v_b_2677_);
lean_dec(v_fvars_2671_);
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2801_);
v___y_2772_ = v___y_2798_;
v___y_2773_ = v_a_2679_;
v___y_2774_ = v_a_2680_;
v___y_2775_ = v_a_2681_;
v___y_2776_ = v_a_2682_;
v___y_2777_ = v_a_2683_;
v___y_2778_ = v_a_2684_;
v___y_2779_ = v_a_2685_;
goto v___jp_2771_;
}
}
}
}
}
else
{
lean_dec(v_a_2703_);
lean_dec_ref(v_b_2677_);
lean_dec(v_n_2674_);
lean_dec_ref(v_e_2672_);
lean_dec(v_fvars_2671_);
return v___x_2704_;
}
}
else
{
lean_dec_ref(v_b_2677_);
lean_dec_ref(v_v_2676_);
lean_dec(v_n_2674_);
lean_dec_ref(v_e_2672_);
lean_dec(v_fvars_2671_);
return v___x_2702_;
}
v___jp_2687_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_inc(v___y_2688_);
v___x_2696_ = l_Lean_Expr_fvar___override(v___y_2688_);
v___x_2697_ = lean_expr_instantiate1(v_b_2677_, v___x_2696_);
lean_dec_ref(v___x_2696_);
lean_dec_ref(v_b_2677_);
v___x_2698_ = lean_box(v_topLevel_2678_);
v___x_2699_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2699_, 0, v_fvars_2671_);
lean_closure_set(v___x_2699_, 1, v___x_2697_);
lean_closure_set(v___x_2699_, 2, v___x_2698_);
v___x_2700_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2688_, v___x_2699_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2688_);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2817_, lean_object* v_struct_2818_, lean_object* v___y_2819_, lean_object* v_typeName_2820_, lean_object* v_idx_2821_, lean_object* v_e_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
uint8_t v___y_42607__boxed_2831_; lean_object* v_res_2832_; 
v___y_42607__boxed_2831_ = lean_unbox(v___y_2819_);
v_res_2832_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2817_, v_struct_2818_, v___y_42607__boxed_2831_, v_typeName_2820_, v_idx_2821_, v_e_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
return v_res_2832_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2836_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2837_ = lean_unsigned_to_nat(75u);
v___x_2838_ = lean_unsigned_to_nat(229u);
v___x_2839_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2840_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2841_ = l_mkPanicMessageWithDecl(v___x_2840_, v___x_2839_, v___x_2838_, v___x_2837_, v___x_2836_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2842_, lean_object* v_e_2843_, lean_object* v_fvars_2844_, uint8_t v___x_2845_, uint8_t v_topLevel_2846_, uint8_t v___y_2847_, lean_object* v_____r_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_k_2858_; 
switch(lean_obj_tag(v_e_2843_))
{
case 5:
{
lean_object* v___x_2861_; lean_object* v_dummy_2862_; lean_object* v_nargs_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2861_ = l_Lean_Expr_getAppFn(v_e_2843_);
v_dummy_2862_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2863_ = l_Lean_Expr_getAppNumArgs(v_e_2843_);
lean_inc(v_nargs_2863_);
v___x_2864_ = lean_mk_array(v_nargs_2863_, v_dummy_2862_);
v___x_2865_ = lean_unsigned_to_nat(1u);
v___x_2866_ = lean_nat_sub(v_nargs_2863_, v___x_2865_);
lean_dec(v_nargs_2863_);
lean_inc_ref(v_e_2843_);
v___x_2867_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2843_, v___x_2864_, v___x_2866_);
v___x_2868_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2868_, 0, v_fvars_2844_);
lean_closure_set(v___x_2868_, 1, v___x_2861_);
lean_closure_set(v___x_2868_, 2, v___x_2867_);
v_k_2858_ = v___x_2868_;
goto v___jp_2857_;
}
case 6:
{
lean_object* v_binderName_2869_; lean_object* v_binderType_2870_; lean_object* v_body_2871_; uint8_t v_binderInfo_2872_; lean_object* v___x_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_binderName_2869_ = lean_ctor_get(v_e_2843_, 0);
v_binderType_2870_ = lean_ctor_get(v_e_2843_, 1);
v_body_2871_ = lean_ctor_get(v_e_2843_, 2);
v_binderInfo_2872_ = lean_ctor_get_uint8(v_e_2843_, sizeof(void*)*3 + 8);
v___x_2873_ = lean_box(v_binderInfo_2872_);
lean_inc_ref(v_e_2843_);
lean_inc_ref_n(v_body_2871_, 2);
lean_inc_n(v_binderName_2869_, 2);
lean_inc_ref_n(v_binderType_2870_, 2);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2874_, 0, v_binderType_2870_);
lean_closure_set(v___f_2874_, 1, v_binderName_2869_);
lean_closure_set(v___f_2874_, 2, v___x_2873_);
lean_closure_set(v___f_2874_, 3, v_body_2871_);
lean_closure_set(v___f_2874_, 4, v_e_2843_);
v___x_2875_ = lean_box(v_binderInfo_2872_);
v___x_2876_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2876_, 0, v_fvars_2844_);
lean_closure_set(v___x_2876_, 1, v_binderName_2869_);
lean_closure_set(v___x_2876_, 2, v_binderType_2870_);
lean_closure_set(v___x_2876_, 3, v_body_2871_);
lean_closure_set(v___x_2876_, 4, v___x_2875_);
lean_closure_set(v___x_2876_, 5, v___f_2874_);
v_k_2858_ = v___x_2876_;
goto v___jp_2857_;
}
case 7:
{
lean_object* v_binderName_2877_; lean_object* v_binderType_2878_; lean_object* v_body_2879_; uint8_t v_binderInfo_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_binderName_2877_ = lean_ctor_get(v_e_2843_, 0);
v_binderType_2878_ = lean_ctor_get(v_e_2843_, 1);
v_body_2879_ = lean_ctor_get(v_e_2843_, 2);
v_binderInfo_2880_ = lean_ctor_get_uint8(v_e_2843_, sizeof(void*)*3 + 8);
v___x_2881_ = lean_box(v_binderInfo_2880_);
lean_inc_ref(v_e_2843_);
lean_inc_ref_n(v_body_2879_, 2);
lean_inc_n(v_binderName_2877_, 2);
lean_inc_ref_n(v_binderType_2878_, 2);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2882_, 0, v_binderType_2878_);
lean_closure_set(v___f_2882_, 1, v_binderName_2877_);
lean_closure_set(v___f_2882_, 2, v___x_2881_);
lean_closure_set(v___f_2882_, 3, v_body_2879_);
lean_closure_set(v___f_2882_, 4, v_e_2843_);
v___x_2883_ = lean_box(v_binderInfo_2880_);
v___x_2884_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2884_, 0, v_fvars_2844_);
lean_closure_set(v___x_2884_, 1, v_binderName_2877_);
lean_closure_set(v___x_2884_, 2, v_binderType_2878_);
lean_closure_set(v___x_2884_, 3, v_body_2879_);
lean_closure_set(v___x_2884_, 4, v___x_2883_);
lean_closure_set(v___x_2884_, 5, v___f_2882_);
v_k_2858_ = v___x_2884_;
goto v___jp_2857_;
}
case 8:
{
uint8_t v_nondep_2885_; 
v_nondep_2885_ = lean_ctor_get_uint8(v_e_2843_, sizeof(void*)*4 + 8);
if (v_nondep_2885_ == 0)
{
lean_object* v_declName_2886_; lean_object* v_type_2887_; lean_object* v_value_2888_; lean_object* v_body_2889_; lean_object* v___x_2890_; 
v_declName_2886_ = lean_ctor_get(v_e_2843_, 0);
lean_inc(v_declName_2886_);
v_type_2887_ = lean_ctor_get(v_e_2843_, 1);
lean_inc_ref(v_type_2887_);
v_value_2888_ = lean_ctor_get(v_e_2843_, 2);
lean_inc_ref(v_value_2888_);
v_body_2889_ = lean_ctor_get(v_e_2843_, 3);
lean_inc_ref(v_body_2889_);
v___x_2890_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2844_, v_e_2843_, v___x_2845_, v_declName_2886_, v_type_2887_, v_value_2888_, v_body_2889_, v_topLevel_2846_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2890_;
}
else
{
lean_object* v_declName_2891_; lean_object* v_type_2892_; lean_object* v_value_2893_; lean_object* v_body_2894_; lean_object* v___x_2895_; 
v_declName_2891_ = lean_ctor_get(v_e_2843_, 0);
lean_inc(v_declName_2891_);
v_type_2892_ = lean_ctor_get(v_e_2843_, 1);
lean_inc_ref(v_type_2892_);
v_value_2893_ = lean_ctor_get(v_e_2843_, 2);
lean_inc_ref(v_value_2893_);
v_body_2894_ = lean_ctor_get(v_e_2843_, 3);
lean_inc_ref(v_body_2894_);
v___x_2895_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2844_, v_e_2843_, v___y_2847_, v_declName_2891_, v_type_2892_, v_value_2893_, v_body_2894_, v_topLevel_2846_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2895_;
}
}
case 10:
{
lean_object* v_data_2896_; lean_object* v_expr_2897_; lean_object* v___x_2898_; 
v_data_2896_ = lean_ctor_get(v_e_2843_, 0);
v_expr_2897_ = lean_ctor_get(v_e_2843_, 1);
lean_inc_ref(v_expr_2897_);
v___x_2898_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2844_, v_expr_2897_, v_topLevel_2846_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2913_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2913_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2913_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
size_t v___x_2903_; size_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = lean_ptr_addr(v_expr_2897_);
v___x_2904_ = lean_ptr_addr(v_a_2899_);
v___x_2905_ = lean_usize_dec_eq(v___x_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
lean_inc(v_data_2896_);
lean_dec_ref_known(v_e_2843_, 2);
v___x_2906_ = l_Lean_Expr_mdata___override(v_data_2896_, v_a_2899_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2906_);
v___x_2908_ = v___x_2901_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
else
{
lean_object* v___x_2911_; 
lean_dec(v_a_2899_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v_e_2843_);
v___x_2911_ = v___x_2901_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_e_2843_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2843_, 2);
return v___x_2898_;
}
}
case 11:
{
lean_object* v_typeName_2914_; lean_object* v_idx_2915_; lean_object* v_struct_2916_; lean_object* v___x_2917_; lean_object* v___f_2918_; 
v_typeName_2914_ = lean_ctor_get(v_e_2843_, 0);
v_idx_2915_ = lean_ctor_get(v_e_2843_, 1);
v_struct_2916_ = lean_ctor_get(v_e_2843_, 2);
v___x_2917_ = lean_box(v___y_2847_);
lean_inc_ref(v_e_2843_);
lean_inc(v_idx_2915_);
lean_inc(v_typeName_2914_);
lean_inc_ref(v_struct_2916_);
v___f_2918_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2918_, 0, v_fvars_2844_);
lean_closure_set(v___f_2918_, 1, v_struct_2916_);
lean_closure_set(v___f_2918_, 2, v___x_2917_);
lean_closure_set(v___f_2918_, 3, v_typeName_2914_);
lean_closure_set(v___f_2918_, 4, v_idx_2915_);
lean_closure_set(v___f_2918_, 5, v_e_2843_);
v_k_2858_ = v___f_2918_;
goto v___jp_2857_;
}
default: 
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec(v_fvars_2844_);
lean_dec_ref(v_e_2843_);
v___x_2919_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2920_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2919_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
return v___x_2920_;
}
}
v___jp_2857_:
{
if (v_descend_2842_ == 0)
{
lean_object* v___x_2859_; 
lean_dec_ref(v_k_2858_);
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_e_2843_);
return v___x_2859_;
}
else
{
lean_object* v___x_2860_; 
lean_dec_ref(v_e_2843_);
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
lean_inc(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
v___x_2860_ = lean_apply_8(v_k_2858_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, lean_box(0));
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2921_, lean_object* v_e_2922_, lean_object* v_fvars_2923_, lean_object* v___x_2924_, lean_object* v_topLevel_2925_, lean_object* v___y_2926_, lean_object* v_____r_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_descend_boxed_2936_; uint8_t v___x_42760__boxed_2937_; uint8_t v_topLevel_boxed_2938_; uint8_t v___y_42761__boxed_2939_; lean_object* v_res_2940_; 
v_descend_boxed_2936_ = lean_unbox(v_descend_2921_);
v___x_42760__boxed_2937_ = lean_unbox(v___x_2924_);
v_topLevel_boxed_2938_ = lean_unbox(v_topLevel_2925_);
v___y_42761__boxed_2939_ = lean_unbox(v___y_2926_);
v_res_2940_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2936_, v_e_2922_, v_fvars_2923_, v___x_42760__boxed_2937_, v_topLevel_boxed_2938_, v___y_42761__boxed_2939_, v_____r_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_2941_, lean_object* v_e_2942_, uint8_t v_topLevel_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___y_2953_; lean_object* v_a_2954_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2964_; lean_object* v___y_2965_; uint8_t v___x_2968_; 
v___x_2968_ = l_Lean_Expr_isAtomic(v_e_2942_);
if (v___x_2968_ == 0)
{
uint8_t v_proofs_2969_; uint8_t v_types_2970_; uint8_t v_descend_2971_; lean_object* v___y_2973_; lean_object* v___y_2974_; uint8_t v___y_2991_; 
v_proofs_2969_ = lean_ctor_get_uint8(v_a_2944_, 0);
v_types_2970_ = lean_ctor_get_uint8(v_a_2944_, 1);
v_descend_2971_ = lean_ctor_get_uint8(v_a_2944_, 3);
if (v_descend_2971_ == 0)
{
if (v_topLevel_2943_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_fvars_2941_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_e_2942_);
return v___x_3014_;
}
else
{
v___y_2991_ = v___x_2968_;
goto v___jp_2990_;
}
}
else
{
v___y_2991_ = v___x_2968_;
goto v___jp_2990_;
}
v___jp_2972_:
{
if (v_proofs_2969_ == 0)
{
lean_object* v___x_2975_; 
lean_inc_ref(v_e_2942_);
v___x_2975_ = l_Lean_Meta_isProof(v_e_2942_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; uint8_t v___x_2977_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2975_, 1);
v___x_2977_ = lean_unbox(v_a_2976_);
lean_dec(v_a_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref(v_e_2942_);
v___x_2978_ = lean_box(0);
lean_inc(v_a_2950_);
lean_inc_ref(v_a_2949_);
lean_inc(v_a_2948_);
lean_inc_ref(v_a_2947_);
lean_inc(v_a_2946_);
lean_inc(v_a_2945_);
lean_inc_ref(v_a_2944_);
v___x_2979_ = lean_apply_9(v___y_2974_, v___x_2978_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, lean_box(0));
v___y_2960_ = v___y_2973_;
v___y_2961_ = v___x_2979_;
goto v___jp_2959_;
}
else
{
lean_dec_ref(v___y_2974_);
v___y_2953_ = v___y_2973_;
v_a_2954_ = v_e_2942_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v_e_2942_);
v_a_2980_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2975_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2975_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v_e_2942_);
v___x_2988_ = lean_box(0);
lean_inc(v_a_2950_);
lean_inc_ref(v_a_2949_);
lean_inc(v_a_2948_);
lean_inc_ref(v_a_2947_);
lean_inc(v_a_2946_);
lean_inc(v_a_2945_);
lean_inc_ref(v_a_2944_);
v___x_2989_ = lean_apply_9(v___y_2974_, v___x_2988_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, lean_box(0));
v___y_2960_ = v___y_2973_;
v___y_2961_ = v___x_2989_;
goto v___jp_2959_;
}
}
v___jp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = lean_box(v_topLevel_2943_);
lean_inc_ref(v_e_2942_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v_e_2942_);
v___x_2994_ = lean_st_ref_get(v_a_2945_);
v___x_2995_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_2994_, v___x_2993_);
lean_dec(v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
uint8_t v___x_2996_; 
v___x_2996_ = l_Lean_Meta_ExtractLets_containsLet(v_e_2942_);
if (v___x_2996_ == 0)
{
lean_dec(v_fvars_2941_);
v___y_2953_ = v___x_2993_;
v_a_2954_ = v_e_2942_;
goto v___jp_2952_;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___f_3003_; 
v___x_2997_ = lean_box(v_descend_2971_);
v___x_2998_ = lean_box(v___x_2996_);
v___x_2999_ = lean_box(v_topLevel_2943_);
v___x_3000_ = lean_box(v___y_2991_);
lean_inc_ref_n(v_e_2942_, 2);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3001_, 0, v___x_2997_);
lean_closure_set(v___f_3001_, 1, v_e_2942_);
lean_closure_set(v___f_3001_, 2, v_fvars_2941_);
lean_closure_set(v___f_3001_, 3, v___x_2998_);
lean_closure_set(v___f_3001_, 4, v___x_2999_);
lean_closure_set(v___f_3001_, 5, v___x_3000_);
v___x_3002_ = lean_box(v_types_2970_);
lean_inc_ref(v___f_3001_);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3003_, 0, v___x_3002_);
lean_closure_set(v___f_3003_, 1, v_e_2942_);
lean_closure_set(v___f_3003_, 2, v___f_3001_);
if (v_topLevel_2943_ == 0)
{
lean_dec_ref(v___f_3001_);
v___y_2973_ = v___x_2993_;
v___y_2974_ = v___f_3003_;
goto v___jp_2972_;
}
else
{
uint8_t v___x_3004_; 
v___x_3004_ = l_Lean_Expr_isLet(v_e_2942_);
if (v___x_3004_ == 0)
{
uint8_t v___x_3005_; 
v___x_3005_ = l_Lean_Expr_isMData(v_e_2942_);
if (v___x_3005_ == 0)
{
lean_dec_ref(v___f_3001_);
v___y_2973_ = v___x_2993_;
v___y_2974_ = v___f_3003_;
goto v___jp_2972_;
}
else
{
lean_dec_ref(v___f_3003_);
lean_dec_ref(v_e_2942_);
v___y_2964_ = v___x_2993_;
v___y_2965_ = v___f_3001_;
goto v___jp_2963_;
}
}
else
{
lean_dec_ref(v___f_3003_);
lean_dec_ref(v_e_2942_);
v___y_2964_ = v___x_2993_;
v___y_2965_ = v___f_3001_;
goto v___jp_2963_;
}
}
}
}
else
{
lean_object* v_val_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec_ref_known(v___x_2993_, 2);
lean_dec_ref(v_e_2942_);
lean_dec(v_fvars_2941_);
v_val_3006_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2995_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_val_3006_);
lean_dec(v___x_2995_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set_tag(v___x_3008_, 0);
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_val_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
else
{
lean_object* v___x_3015_; 
lean_dec(v_fvars_2941_);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_e_2942_);
return v___x_3015_;
}
v___jp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2955_ = lean_st_ref_take(v_a_2945_);
lean_inc_ref(v_a_2954_);
v___x_2956_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_2955_, v___y_2953_, v_a_2954_);
v___x_2957_ = lean_st_ref_put(v_a_2945_, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_a_2954_);
return v___x_2958_;
}
v___jp_2959_:
{
if (lean_obj_tag(v___y_2961_) == 0)
{
lean_object* v_a_2962_; 
v_a_2962_ = lean_ctor_get(v___y_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___y_2961_, 1);
v___y_2953_ = v___y_2960_;
v_a_2954_ = v_a_2962_;
goto v___jp_2952_;
}
else
{
lean_dec_ref(v___y_2960_);
return v___y_2961_;
}
}
v___jp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_box(0);
lean_inc(v_a_2950_);
lean_inc_ref(v_a_2949_);
lean_inc(v_a_2948_);
lean_inc_ref(v_a_2947_);
lean_inc(v_a_2946_);
lean_inc(v_a_2945_);
lean_inc_ref(v_a_2944_);
v___x_2967_ = lean_apply_9(v___y_2965_, v___x_2966_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, lean_box(0));
v___y_2960_ = v___y_2964_;
v___y_2961_ = v___x_2967_;
goto v___jp_2959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3016_, lean_object* v_struct_3017_, uint8_t v___y_3018_, lean_object* v_typeName_3019_, lean_object* v_idx_3020_, lean_object* v_e_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
lean_inc_ref(v_struct_3017_);
v___x_3030_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3016_, v_struct_3017_, v___y_3018_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3045_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3045_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3045_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
size_t v___x_3035_; size_t v___x_3036_; uint8_t v___x_3037_; 
v___x_3035_ = lean_ptr_addr(v_struct_3017_);
lean_dec_ref(v_struct_3017_);
v___x_3036_ = lean_ptr_addr(v_a_3031_);
v___x_3037_ = lean_usize_dec_eq(v___x_3035_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec_ref(v_e_3021_);
v___x_3038_ = l_Lean_Expr_proj___override(v_typeName_3019_, v_idx_3020_, v_a_3031_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3038_);
v___x_3040_ = v___x_3033_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
else
{
lean_object* v___x_3043_; 
lean_dec(v_a_3031_);
lean_dec(v_idx_3020_);
lean_dec(v_typeName_3019_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v_e_3021_);
v___x_3043_ = v___x_3033_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_e_3021_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_dec_ref(v_e_3021_);
lean_dec(v_idx_3020_);
lean_dec(v_typeName_3019_);
lean_dec_ref(v_struct_3017_);
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3046_, lean_object* v_sz_3047_, lean_object* v_i_3048_, lean_object* v_bs_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
size_t v_sz_boxed_3058_; size_t v_i_boxed_3059_; lean_object* v_res_3060_; 
v_sz_boxed_3058_ = lean_unbox_usize(v_sz_3047_);
lean_dec(v_sz_3047_);
v_i_boxed_3059_ = lean_unbox_usize(v_i_3048_);
lean_dec(v_i_3048_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3046_, v_sz_boxed_3058_, v_i_boxed_3059_, v_bs_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3061_, lean_object* v_fst_3062_, lean_object* v_fvars_3063_, lean_object* v_a_3064_, lean_object* v_b_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3061_, v_fst_3062_, v_fvars_3063_, v_a_3064_, v_b_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec_ref(v_fst_3062_);
lean_dec(v_upperBound_3061_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3075_, lean_object* v_e_3076_, lean_object* v_isLet_3077_, lean_object* v_n_3078_, lean_object* v_t_3079_, lean_object* v_v_3080_, lean_object* v_b_3081_, lean_object* v_topLevel_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
uint8_t v_isLet_boxed_3091_; uint8_t v_topLevel_boxed_3092_; lean_object* v_res_3093_; 
v_isLet_boxed_3091_ = lean_unbox(v_isLet_3077_);
v_topLevel_boxed_3092_ = lean_unbox(v_topLevel_3082_);
v_res_3093_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3075_, v_e_3076_, v_isLet_boxed_3091_, v_n_3078_, v_t_3079_, v_v_3080_, v_b_3081_, v_topLevel_boxed_3092_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3094_, lean_object* v_name_3095_, lean_object* v_type_3096_, lean_object* v_val_3097_, lean_object* v_k_3098_, uint8_t v_nondep_3099_, uint8_t v_kind_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3095_, v_type_3096_, v_val_3097_, v_k_3098_, v_nondep_3099_, v_kind_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3110_, lean_object* v_name_3111_, lean_object* v_type_3112_, lean_object* v_val_3113_, lean_object* v_k_3114_, lean_object* v_nondep_3115_, lean_object* v_kind_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
uint8_t v_nondep_boxed_3125_; uint8_t v_kind_boxed_3126_; lean_object* v_res_3127_; 
v_nondep_boxed_3125_ = lean_unbox(v_nondep_3115_);
v_kind_boxed_3126_ = lean_unbox(v_kind_3116_);
v_res_3127_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3110_, v_name_3111_, v_type_3112_, v_val_3113_, v_k_3114_, v_nondep_boxed_3125_, v_kind_boxed_3126_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3128_, lean_object* v_m_3129_, lean_object* v_a_3130_, lean_object* v_b_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3129_, v_a_3130_, v_b_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3133_, lean_object* v_m_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3134_, v_a_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3137_, lean_object* v_m_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3137_, v_m_3138_, v_a_3139_);
lean_dec_ref(v_a_3139_);
lean_dec_ref(v_m_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3141_, lean_object* v_fst_3142_, lean_object* v_fvars_3143_, lean_object* v_inst_3144_, lean_object* v_R_3145_, lean_object* v_a_3146_, lean_object* v_b_3147_, lean_object* v_c_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3141_, v_fst_3142_, v_fvars_3143_, v_a_3146_, v_b_3147_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3158_, lean_object* v_fst_3159_, lean_object* v_fvars_3160_, lean_object* v_inst_3161_, lean_object* v_R_3162_, lean_object* v_a_3163_, lean_object* v_b_3164_, lean_object* v_c_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3158_, v_fst_3159_, v_fvars_3160_, v_inst_3161_, v_R_3162_, v_a_3163_, v_b_3164_, v_c_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec_ref(v_fst_3159_);
lean_dec(v_upperBound_3158_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3175_, lean_object* v_m_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3176_, v_a_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3179_, lean_object* v_m_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3179_, v_m_3180_, v_a_3181_);
lean_dec_ref(v_a_3181_);
lean_dec_ref(v_m_3180_);
return v_res_3182_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3183_, lean_object* v_a_3184_, lean_object* v_x_3185_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3184_, v_x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3187_, lean_object* v_a_3188_, lean_object* v_x_3189_){
_start:
{
uint8_t v_res_3190_; lean_object* v_r_3191_; 
v_res_3190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3187_, v_a_3188_, v_x_3189_);
lean_dec(v_x_3189_);
lean_dec_ref(v_a_3188_);
v_r_3191_ = lean_box(v_res_3190_);
return v_r_3191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3192_, lean_object* v_data_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3195_, lean_object* v_a_3196_, lean_object* v_b_3197_, lean_object* v_x_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3196_, v_b_3197_, v_x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3200_, lean_object* v_a_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3201_, v_x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3204_, lean_object* v_a_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3204_, v_a_3205_, v_x_3206_);
lean_dec(v_x_3206_);
lean_dec_ref(v_a_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3208_, lean_object* v_a_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3209_, v_x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3212_, lean_object* v_a_3213_, lean_object* v_x_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3212_, v_a_3213_, v_x_3214_);
lean_dec(v_x_3214_);
lean_dec_ref(v_a_3213_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3216_, lean_object* v_i_3217_, lean_object* v_source_3218_, lean_object* v_target_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3217_, v_source_3218_, v_target_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3222_, v_x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v___x_3234_; lean_object* v_a_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; lean_object* v___x_3238_; 
v___x_3234_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3225_, v_a_3230_);
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref(v___x_3234_);
v___x_3236_ = lean_box(0);
v___x_3237_ = 1;
v___x_3238_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3236_, v_a_3235_, v___x_3237_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3243_);
lean_dec(v_a_3242_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3249_, size_t v_i_3250_, lean_object* v_bs_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_usize_dec_lt(v_i_3250_, v_sz_3249_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_bs_3251_);
return v___x_3261_;
}
else
{
lean_object* v_v_3262_; lean_object* v___x_3263_; lean_object* v_bs_x27_3264_; lean_object* v___x_3265_; 
v_v_3262_ = lean_array_uget(v_bs_3251_, v_i_3250_);
v___x_3263_ = lean_unsigned_to_nat(0u);
v_bs_x27_3264_ = lean_array_uset(v_bs_3251_, v_i_3250_, v___x_3263_);
v___x_3265_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3262_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; size_t v___x_3267_; size_t v___x_3268_; lean_object* v___x_3269_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = ((size_t)1ULL);
v___x_3268_ = lean_usize_add(v_i_3250_, v___x_3267_);
v___x_3269_ = lean_array_uset(v_bs_x27_3264_, v_i_3250_, v_a_3266_);
v_i_3250_ = v___x_3268_;
v_bs_3251_ = v___x_3269_;
goto _start;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v_bs_x27_3264_);
v_a_3271_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3265_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3265_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3279_, lean_object* v_i_3280_, lean_object* v_bs_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
size_t v_sz_boxed_3290_; size_t v_i_boxed_3291_; lean_object* v_res_3292_; 
v_sz_boxed_3290_ = lean_unbox_usize(v_sz_3279_);
lean_dec(v_sz_3279_);
v_i_boxed_3291_ = lean_unbox_usize(v_i_3280_);
lean_dec(v_i_3280_);
v_res_3292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3290_, v_i_boxed_3291_, v_bs_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; uint8_t v_merge_3313_; 
v_merge_3313_ = lean_ctor_get_uint8(v_a_3294_, 6);
if (v_merge_3313_ == 0)
{
v___y_3303_ = v_a_3294_;
v___y_3304_ = v_a_3295_;
v___y_3305_ = v_a_3296_;
v___y_3306_ = v_a_3297_;
v___y_3307_ = v_a_3298_;
v___y_3308_ = v_a_3299_;
v___y_3309_ = v_a_3300_;
goto v___jp_3302_;
}
else
{
uint8_t v_useContext_3314_; 
v_useContext_3314_ = lean_ctor_get_uint8(v_a_3294_, 7);
if (v_useContext_3314_ == 0)
{
v___y_3303_ = v_a_3294_;
v___y_3304_ = v_a_3295_;
v___y_3305_ = v_a_3296_;
v___y_3306_ = v_a_3297_;
v___y_3307_ = v_a_3298_;
v___y_3308_ = v_a_3299_;
v___y_3309_ = v_a_3300_;
goto v___jp_3302_;
}
else
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_dec_ref_known(v___x_3315_, 1);
v___y_3303_ = v_a_3294_;
v___y_3304_ = v_a_3295_;
v___y_3305_ = v_a_3296_;
v___y_3306_ = v_a_3297_;
v___y_3307_ = v_a_3298_;
v___y_3308_ = v_a_3299_;
v___y_3309_ = v_a_3300_;
goto v___jp_3302_;
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec_ref(v_es_3293_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
v___jp_3302_:
{
size_t v_sz_3310_; size_t v___x_3311_; lean_object* v___x_3312_; 
v_sz_3310_ = lean_array_size(v_es_3293_);
v___x_3311_ = ((size_t)0ULL);
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3310_, v___x_3311_, v_es_3293_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Meta_ExtractLets_extract(v_es_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3325_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
v_a_3350_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3341_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3341_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3358_, v_x_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3366_, lean_object* v_decls_3367_, lean_object* v_x_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3367_, v_x_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3375_, lean_object* v_decls_3376_, lean_object* v_x_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3375_, v_decls_3376_, v_x_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3384_, size_t v_i_3385_, lean_object* v_bs_3386_){
_start:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_usize_dec_lt(v_i_3385_, v_sz_3384_);
if (v___x_3387_ == 0)
{
return v_bs_3386_;
}
else
{
lean_object* v_v_3388_; lean_object* v___x_3389_; lean_object* v_bs_x27_3390_; lean_object* v___x_3391_; size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
v_v_3388_ = lean_array_uget(v_bs_3386_, v_i_3385_);
v___x_3389_ = lean_unsigned_to_nat(0u);
v_bs_x27_3390_ = lean_array_uset(v_bs_3386_, v_i_3385_, v___x_3389_);
v___x_3391_ = l_Lean_LocalDecl_fvarId(v_v_3388_);
lean_dec(v_v_3388_);
v___x_3392_ = ((size_t)1ULL);
v___x_3393_ = lean_usize_add(v_i_3385_, v___x_3392_);
v___x_3394_ = lean_array_uset(v_bs_x27_3390_, v_i_3385_, v___x_3391_);
v_i_3385_ = v___x_3393_;
v_bs_3386_ = v___x_3394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3396_, lean_object* v_i_3397_, lean_object* v_bs_3398_){
_start:
{
size_t v_sz_boxed_3399_; size_t v_i_boxed_3400_; lean_object* v_res_3401_; 
v_sz_boxed_3399_ = lean_unbox_usize(v_sz_3396_);
lean_dec(v_sz_3396_);
v_i_boxed_3400_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3399_, v_i_boxed_3400_, v_bs_3398_);
return v_res_3401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = lean_box(0);
v___x_3403_ = lean_unsigned_to_nat(16u);
v___x_3404_ = lean_mk_array(v___x_3403_, v___x_3402_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3406_ = lean_unsigned_to_nat(0u);
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v___x_3405_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3408_, lean_object* v_givenNames_3409_, lean_object* v_k_3410_, lean_object* v_config_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3418_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3419_, 0, v_givenNames_3409_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
lean_ctor_set(v___x_3419_, 2, v___x_3417_);
v___x_3420_ = lean_st_mk_ref(v___x_3419_);
v___x_3421_ = lean_st_mk_ref(v___x_3417_);
v___x_3422_ = l_Lean_Meta_ExtractLets_extract(v_es_3408_, v_config_3411_, v___x_3421_, v___x_3420_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v_givenNames_3426_; lean_object* v_decls_3427_; size_t v_sz_3428_; size_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; size_t v_sz_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3422_, 1);
v___x_3424_ = lean_st_ref_get(v___x_3421_);
lean_dec(v___x_3421_);
lean_dec(v___x_3424_);
v___x_3425_ = lean_st_ref_get(v___x_3420_);
lean_dec(v___x_3420_);
v_givenNames_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_givenNames_3426_);
v_decls_3427_ = lean_ctor_get(v___x_3425_, 1);
lean_inc_ref(v_decls_3427_);
lean_dec(v___x_3425_);
v_sz_3428_ = lean_array_size(v_decls_3427_);
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_3428_, v___x_3429_, v_decls_3427_);
lean_inc_ref(v___x_3430_);
v___x_3431_ = lean_array_to_list(v___x_3430_);
v_sz_3432_ = lean_array_size(v___x_3430_);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3432_, v___x_3429_, v___x_3430_);
v___x_3434_ = lean_apply_3(v_k_3410_, v___x_3433_, v_a_3423_, v_givenNames_3426_);
v___x_3435_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3431_, v___x_3434_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_);
return v___x_3435_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v___x_3421_);
lean_dec(v___x_3420_);
lean_dec_ref(v_k_3410_);
v_a_3436_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3422_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3422_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3444_, lean_object* v_givenNames_3445_, lean_object* v_k_3446_, lean_object* v_config_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3444_, v_givenNames_3445_, v_k_3446_, v_config_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec_ref(v_config_3447_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3454_, lean_object* v_es_3455_, lean_object* v_givenNames_3456_, lean_object* v_k_3457_, lean_object* v_config_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3455_, v_givenNames_3456_, v_k_3457_, v_config_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3465_, lean_object* v_es_3466_, lean_object* v_givenNames_3467_, lean_object* v_k_3468_, lean_object* v_config_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3465_, v_es_3466_, v_givenNames_3467_, v_k_3468_, v_config_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec_ref(v_config_3469_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3476_, lean_object* v_runInBase_3477_, lean_object* v_b_3478_, lean_object* v_c_3479_, lean_object* v_d_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_apply_3(v_k_3476_, v_b_3478_, v_c_3479_, v_d_3480_);
lean_inc(v___y_3484_);
lean_inc_ref(v___y_3483_);
lean_inc(v___y_3482_);
lean_inc_ref(v___y_3481_);
v___x_3487_ = lean_apply_7(v_runInBase_3477_, lean_box(0), v___x_3486_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, lean_box(0));
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3488_, lean_object* v_runInBase_3489_, lean_object* v_b_3490_, lean_object* v_c_3491_, lean_object* v_d_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3488_, v_runInBase_3489_, v_b_3490_, v_c_3491_, v_d_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3499_, lean_object* v_es_3500_, lean_object* v_givenNames_3501_, lean_object* v_config_3502_, lean_object* v_runInBase_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___f_3509_; lean_object* v___x_3510_; 
v___f_3509_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3509_, 0, v_k_3499_);
lean_closure_set(v___f_3509_, 1, v_runInBase_3503_);
v___x_3510_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3500_, v_givenNames_3501_, v___f_3509_, v_config_3502_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3511_, lean_object* v_es_3512_, lean_object* v_givenNames_3513_, lean_object* v_config_3514_, lean_object* v_runInBase_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3511_, v_es_3512_, v_givenNames_3513_, v_config_3514_, v_runInBase_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v_config_3514_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_es_3524_, lean_object* v_givenNames_3525_, lean_object* v_k_3526_, lean_object* v_config_3527_){
_start:
{
lean_object* v_toBind_3528_; lean_object* v_liftWith_3529_; lean_object* v_restoreM_3530_; lean_object* v___f_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_toBind_3528_ = lean_ctor_get(v_inst_3522_, 1);
lean_inc(v_toBind_3528_);
lean_dec_ref(v_inst_3522_);
v_liftWith_3529_ = lean_ctor_get(v_inst_3523_, 0);
lean_inc(v_liftWith_3529_);
v_restoreM_3530_ = lean_ctor_get(v_inst_3523_, 1);
lean_inc(v_restoreM_3530_);
lean_dec_ref(v_inst_3523_);
v___f_3531_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3531_, 0, v_k_3526_);
lean_closure_set(v___f_3531_, 1, v_es_3524_);
lean_closure_set(v___f_3531_, 2, v_givenNames_3525_);
lean_closure_set(v___f_3531_, 3, v_config_3527_);
v___x_3532_ = lean_apply_2(v_liftWith_3529_, lean_box(0), v___f_3531_);
v___x_3533_ = lean_apply_1(v_restoreM_3530_, lean_box(0));
v___x_3534_ = lean_apply_4(v_toBind_3528_, lean_box(0), lean_box(0), v___x_3532_, v___x_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3535_, lean_object* v_00_u03b1_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_es_3539_, lean_object* v_givenNames_3540_, lean_object* v_k_3541_, lean_object* v_config_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_Meta_extractLets___redArg(v_inst_3537_, v_inst_3538_, v_es_3539_, v_givenNames_3540_, v_k_3541_, v_config_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3545_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3546_ = lean_box(0);
v___x_3547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v___x_3545_);
lean_ctor_set(v___x_3547_, 2, v___x_3544_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3548_, lean_object* v_config_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
uint8_t v_proofs_3555_; uint8_t v_types_3556_; uint8_t v_implicits_3557_; uint8_t v_descend_3558_; uint8_t v_underBinder_3559_; uint8_t v_usedOnly_3560_; uint8_t v_merge_3561_; uint8_t v_useContext_3562_; uint8_t v_preserveBinderNames_3563_; uint8_t v_lift_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3603_; 
v_proofs_3555_ = lean_ctor_get_uint8(v_config_3549_, 0);
v_types_3556_ = lean_ctor_get_uint8(v_config_3549_, 1);
v_implicits_3557_ = lean_ctor_get_uint8(v_config_3549_, 2);
v_descend_3558_ = lean_ctor_get_uint8(v_config_3549_, 3);
v_underBinder_3559_ = lean_ctor_get_uint8(v_config_3549_, 4);
v_usedOnly_3560_ = lean_ctor_get_uint8(v_config_3549_, 5);
v_merge_3561_ = lean_ctor_get_uint8(v_config_3549_, 6);
v_useContext_3562_ = lean_ctor_get_uint8(v_config_3549_, 7);
v_preserveBinderNames_3563_ = lean_ctor_get_uint8(v_config_3549_, 9);
v_lift_3564_ = lean_ctor_get_uint8(v_config_3549_, 10);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_config_3549_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3566_ = v_config_3549_;
v_isShared_3567_ = v_isSharedCheck_3603_;
goto v_resetjp_3565_;
}
else
{
lean_dec(v_config_3549_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3603_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; lean_object* v___x_3574_; 
v___x_3568_ = l_Lean_instInhabitedExpr;
v___x_3569_ = lean_unsigned_to_nat(1u);
v___x_3570_ = lean_mk_empty_array_with_capacity(v___x_3569_);
v___x_3571_ = lean_array_push(v___x_3570_, v_e_3548_);
v___x_3572_ = 1;
if (v_isShared_3567_ == 0)
{
v___x_3574_ = v___x_3566_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 0, v_proofs_3555_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 1, v_types_3556_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 2, v_implicits_3557_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 3, v_descend_3558_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 4, v_underBinder_3559_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 5, v_usedOnly_3560_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 6, v_merge_3561_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 7, v_useContext_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 9, v_preserveBinderNames_3563_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, 10, v_lift_3564_);
v___x_3574_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_ctor_set_uint8(v___x_3574_, 8, v___x_3572_);
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3577_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3578_ = lean_st_mk_ref(v___x_3577_);
v___x_3579_ = lean_st_mk_ref(v___x_3576_);
v___x_3580_ = l_Lean_Meta_ExtractLets_extract(v___x_3571_, v___x_3574_, v___x_3579_, v___x_3578_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
lean_dec_ref(v___x_3574_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3593_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3593_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3593_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v_decls_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3585_ = lean_st_ref_get(v___x_3579_);
lean_dec(v___x_3579_);
lean_dec(v___x_3585_);
v___x_3586_ = lean_st_ref_get(v___x_3578_);
lean_dec(v___x_3578_);
v_decls_3587_ = lean_ctor_get(v___x_3586_, 1);
lean_inc_ref(v_decls_3587_);
lean_dec(v___x_3586_);
v___x_3588_ = lean_array_get(v___x_3568_, v_a_3581_, v___x_3575_);
lean_dec(v_a_3581_);
v___x_3589_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3587_, v___x_3588_);
lean_dec_ref(v_decls_3587_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3589_);
v___x_3591_ = v___x_3583_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v___x_3579_);
lean_dec(v___x_3578_);
v_a_3594_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3580_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3580_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3604_, lean_object* v_config_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Meta_liftLets(v_e_3604_, v_config_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
return v_res_3611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3614_ = l_Lean_stringToMessageData(v___x_3613_);
return v___x_3614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3617_, lean_object* v_mvarId_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3625_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3617_, v_mvarId_3618_, v___x_3624_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3626_, lean_object* v_mvarId_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3626_, v_mvarId_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3634_, lean_object* v_tactic_3635_, lean_object* v_mvarId_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3635_, v_mvarId_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_tactic_3644_, lean_object* v_mvarId_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3643_, v_tactic_3644_, v_mvarId_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3652_, lean_object* v_b_3653_, lean_object* v_c_3654_, lean_object* v_d_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
lean_inc(v___y_3659_);
lean_inc_ref(v___y_3658_);
lean_inc(v___y_3657_);
lean_inc_ref(v___y_3656_);
v___x_3661_ = lean_apply_8(v_k_3652_, v_b_3653_, v_c_3654_, v_d_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, lean_box(0));
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3662_, lean_object* v_b_3663_, lean_object* v_c_3664_, lean_object* v_d_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3662_, v_b_3663_, v_c_3664_, v_d_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3672_, lean_object* v_givenNames_3673_, lean_object* v_k_3674_, lean_object* v_config_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___f_3681_; lean_object* v___x_3682_; 
v___f_3681_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3681_, 0, v_k_3674_);
v___x_3682_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3672_, v_givenNames_3673_, v___f_3681_, v_config_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
v_a_3691_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3682_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3682_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3699_, lean_object* v_givenNames_3700_, lean_object* v_k_3701_, lean_object* v_config_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3699_, v_givenNames_3700_, v_k_3701_, v_config_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v_config_3702_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3709_, lean_object* v_es_3710_, lean_object* v_givenNames_3711_, lean_object* v_k_3712_, lean_object* v_config_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3710_, v_givenNames_3711_, v_k_3712_, v_config_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3720_, lean_object* v_es_3721_, lean_object* v_givenNames_3722_, lean_object* v_k_3723_, lean_object* v_config_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3720_, v_es_3721_, v_givenNames_3722_, v_k_3723_, v_config_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec_ref(v_config_3724_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3731_, lean_object* v_x_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3731_, v_x_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v_a_3747_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3738_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3738_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3755_, lean_object* v_x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3755_, v_x_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3763_, lean_object* v_mvarId_3764_, lean_object* v_x_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3764_, v_x_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3772_, lean_object* v_mvarId_3773_, lean_object* v_x_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3772_, v_mvarId_3773_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_){
_start:
{
lean_object* v_ks_3785_; lean_object* v_vs_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3810_; 
v_ks_3785_ = lean_ctor_get(v_x_3781_, 0);
v_vs_3786_ = lean_ctor_get(v_x_3781_, 1);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_x_3781_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3788_ = v_x_3781_;
v_isShared_3789_ = v_isSharedCheck_3810_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_vs_3786_);
lean_inc(v_ks_3785_);
lean_dec(v_x_3781_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3810_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; uint8_t v___x_3791_; 
v___x_3790_ = lean_array_get_size(v_ks_3785_);
v___x_3791_ = lean_nat_dec_lt(v_x_3782_, v___x_3790_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_dec(v_x_3782_);
v___x_3792_ = lean_array_push(v_ks_3785_, v_x_3783_);
v___x_3793_ = lean_array_push(v_vs_3786_, v_x_3784_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v___x_3793_);
lean_ctor_set(v___x_3788_, 0, v___x_3792_);
v___x_3795_ = v___x_3788_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3792_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
else
{
lean_object* v_k_x27_3797_; uint8_t v___x_3798_; 
v_k_x27_3797_ = lean_array_fget_borrowed(v_ks_3785_, v_x_3782_);
v___x_3798_ = l_Lean_instBEqMVarId_beq(v_x_3783_, v_k_x27_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3800_; 
if (v_isShared_3789_ == 0)
{
v___x_3800_ = v___x_3788_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_ks_3785_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_vs_3786_);
v___x_3800_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_unsigned_to_nat(1u);
v___x_3802_ = lean_nat_add(v_x_3782_, v___x_3801_);
lean_dec(v_x_3782_);
v_x_3781_ = v___x_3800_;
v_x_3782_ = v___x_3802_;
goto _start;
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
v___x_3805_ = lean_array_fset(v_ks_3785_, v_x_3782_, v_x_3783_);
v___x_3806_ = lean_array_fset(v_vs_3786_, v_x_3782_, v_x_3784_);
lean_dec(v_x_3782_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v___x_3806_);
lean_ctor_set(v___x_3788_, 0, v___x_3805_);
v___x_3808_ = v___x_3788_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3811_, lean_object* v_k_3812_, lean_object* v_v_3813_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_unsigned_to_nat(0u);
v___x_3815_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3811_, v___x_3814_, v_k_3812_, v_v_3813_);
return v___x_3815_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3817_, size_t v_x_3818_, size_t v_x_3819_, lean_object* v_x_3820_, lean_object* v_x_3821_){
_start:
{
if (lean_obj_tag(v_x_3817_) == 0)
{
lean_object* v_es_3822_; size_t v___x_3823_; size_t v___x_3824_; lean_object* v_j_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_es_3822_ = lean_ctor_get(v_x_3817_, 0);
v___x_3823_ = ((size_t)31ULL);
v___x_3824_ = lean_usize_land(v_x_3818_, v___x_3823_);
v_j_3825_ = lean_usize_to_nat(v___x_3824_);
v___x_3826_ = lean_array_get_size(v_es_3822_);
v___x_3827_ = lean_nat_dec_lt(v_j_3825_, v___x_3826_);
if (v___x_3827_ == 0)
{
lean_dec(v_j_3825_);
lean_dec(v_x_3821_);
lean_dec(v_x_3820_);
return v_x_3817_;
}
else
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3866_; 
lean_inc_ref(v_es_3822_);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_x_3817_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; 
v_unused_3867_ = lean_ctor_get(v_x_3817_, 0);
lean_dec(v_unused_3867_);
v___x_3829_ = v_x_3817_;
v_isShared_3830_ = v_isSharedCheck_3866_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v_x_3817_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3866_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v_v_3831_; lean_object* v___x_3832_; lean_object* v_xs_x27_3833_; lean_object* v___y_3835_; 
v_v_3831_ = lean_array_fget(v_es_3822_, v_j_3825_);
v___x_3832_ = lean_box(0);
v_xs_x27_3833_ = lean_array_fset(v_es_3822_, v_j_3825_, v___x_3832_);
switch(lean_obj_tag(v_v_3831_))
{
case 0:
{
lean_object* v_key_3840_; lean_object* v_val_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3851_; 
v_key_3840_ = lean_ctor_get(v_v_3831_, 0);
v_val_3841_ = lean_ctor_get(v_v_3831_, 1);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_v_3831_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3843_ = v_v_3831_;
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_val_3841_);
lean_inc(v_key_3840_);
lean_dec(v_v_3831_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
uint8_t v___x_3845_; 
v___x_3845_ = l_Lean_instBEqMVarId_beq(v_x_3820_, v_key_3840_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
lean_del_object(v___x_3843_);
v___x_3846_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3840_, v_val_3841_, v_x_3820_, v_x_3821_);
v___x_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
v___y_3835_ = v___x_3847_;
goto v___jp_3834_;
}
else
{
lean_object* v___x_3849_; 
lean_dec(v_val_3841_);
lean_dec(v_key_3840_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 1, v_x_3821_);
lean_ctor_set(v___x_3843_, 0, v_x_3820_);
v___x_3849_ = v___x_3843_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_x_3820_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_x_3821_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
v___y_3835_ = v___x_3849_;
goto v___jp_3834_;
}
}
}
}
case 1:
{
lean_object* v_node_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3864_; 
v_node_3852_ = lean_ctor_get(v_v_3831_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_v_3831_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3854_ = v_v_3831_;
v_isShared_3855_ = v_isSharedCheck_3864_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_node_3852_);
lean_dec(v_v_3831_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3864_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
size_t v___x_3856_; size_t v___x_3857_; size_t v___x_3858_; size_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3862_; 
v___x_3856_ = ((size_t)5ULL);
v___x_3857_ = lean_usize_shift_right(v_x_3818_, v___x_3856_);
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_add(v_x_3819_, v___x_3858_);
v___x_3860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3852_, v___x_3857_, v___x_3859_, v_x_3820_, v_x_3821_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3860_);
v___x_3862_ = v___x_3854_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
v___y_3835_ = v___x_3862_;
goto v___jp_3834_;
}
}
}
default: 
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v_x_3820_);
lean_ctor_set(v___x_3865_, 1, v_x_3821_);
v___y_3835_ = v___x_3865_;
goto v___jp_3834_;
}
}
v___jp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3836_ = lean_array_fset(v_xs_x27_3833_, v_j_3825_, v___y_3835_);
lean_dec(v_j_3825_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v___x_3836_);
v___x_3838_ = v___x_3829_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
else
{
lean_object* v_ks_3868_; lean_object* v_vs_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3887_; 
v_ks_3868_ = lean_ctor_get(v_x_3817_, 0);
v_vs_3869_ = lean_ctor_get(v_x_3817_, 1);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_x_3817_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3871_ = v_x_3817_;
v_isShared_3872_ = v_isSharedCheck_3887_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_vs_3869_);
lean_inc(v_ks_3868_);
lean_dec(v_x_3817_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3887_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_ks_3868_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_vs_3869_);
v___x_3874_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v_newNode_3875_; size_t v___x_3876_; uint8_t v___x_3877_; 
v_newNode_3875_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3874_, v_x_3820_, v_x_3821_);
v___x_3876_ = ((size_t)7ULL);
v___x_3877_ = lean_usize_dec_le(v___x_3876_, v_x_3819_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3878_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3875_);
v___x_3879_ = lean_unsigned_to_nat(4u);
v___x_3880_ = lean_nat_dec_lt(v___x_3878_, v___x_3879_);
lean_dec(v___x_3878_);
if (v___x_3880_ == 0)
{
lean_object* v_ks_3881_; lean_object* v_vs_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_ks_3881_ = lean_ctor_get(v_newNode_3875_, 0);
lean_inc_ref(v_ks_3881_);
v_vs_3882_ = lean_ctor_get(v_newNode_3875_, 1);
lean_inc_ref(v_vs_3882_);
lean_dec_ref(v_newNode_3875_);
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3885_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3819_, v_ks_3881_, v_vs_3882_, v___x_3883_, v___x_3884_);
lean_dec_ref(v_vs_3882_);
lean_dec_ref(v_ks_3881_);
return v___x_3885_;
}
else
{
return v_newNode_3875_;
}
}
else
{
return v_newNode_3875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3888_, lean_object* v_keys_3889_, lean_object* v_vals_3890_, lean_object* v_i_3891_, lean_object* v_entries_3892_){
_start:
{
lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = lean_array_get_size(v_keys_3889_);
v___x_3894_ = lean_nat_dec_lt(v_i_3891_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_dec(v_i_3891_);
return v_entries_3892_;
}
else
{
lean_object* v_k_3895_; lean_object* v_v_3896_; uint64_t v___x_3897_; size_t v_h_3898_; size_t v___x_3899_; lean_object* v___x_3900_; size_t v___x_3901_; size_t v___x_3902_; size_t v___x_3903_; size_t v_h_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_k_3895_ = lean_array_fget_borrowed(v_keys_3889_, v_i_3891_);
v_v_3896_ = lean_array_fget_borrowed(v_vals_3890_, v_i_3891_);
v___x_3897_ = l_Lean_instHashableMVarId_hash(v_k_3895_);
v_h_3898_ = lean_uint64_to_usize(v___x_3897_);
v___x_3899_ = ((size_t)5ULL);
v___x_3900_ = lean_unsigned_to_nat(1u);
v___x_3901_ = ((size_t)1ULL);
v___x_3902_ = lean_usize_sub(v_depth_3888_, v___x_3901_);
v___x_3903_ = lean_usize_mul(v___x_3899_, v___x_3902_);
v_h_3904_ = lean_usize_shift_right(v_h_3898_, v___x_3903_);
v___x_3905_ = lean_nat_add(v_i_3891_, v___x_3900_);
lean_dec(v_i_3891_);
lean_inc(v_v_3896_);
lean_inc(v_k_3895_);
v___x_3906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3892_, v_h_3904_, v_depth_3888_, v_k_3895_, v_v_3896_);
v_i_3891_ = v___x_3905_;
v_entries_3892_ = v___x_3906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3908_, lean_object* v_keys_3909_, lean_object* v_vals_3910_, lean_object* v_i_3911_, lean_object* v_entries_3912_){
_start:
{
size_t v_depth_boxed_3913_; lean_object* v_res_3914_; 
v_depth_boxed_3913_ = lean_unbox_usize(v_depth_3908_);
lean_dec(v_depth_3908_);
v_res_3914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3913_, v_keys_3909_, v_vals_3910_, v_i_3911_, v_entries_3912_);
lean_dec_ref(v_vals_3910_);
lean_dec_ref(v_keys_3909_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_){
_start:
{
size_t v_x_2302__boxed_3920_; size_t v_x_2303__boxed_3921_; lean_object* v_res_3922_; 
v_x_2302__boxed_3920_ = lean_unbox_usize(v_x_3916_);
lean_dec(v_x_3916_);
v_x_2303__boxed_3921_ = lean_unbox_usize(v_x_3917_);
lean_dec(v_x_3917_);
v_res_3922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3915_, v_x_2302__boxed_3920_, v_x_2303__boxed_3921_, v_x_3918_, v_x_3919_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3923_, lean_object* v_x_3924_, lean_object* v_x_3925_){
_start:
{
uint64_t v___x_3926_; size_t v___x_3927_; size_t v___x_3928_; lean_object* v___x_3929_; 
v___x_3926_ = l_Lean_instHashableMVarId_hash(v_x_3924_);
v___x_3927_ = lean_uint64_to_usize(v___x_3926_);
v___x_3928_ = ((size_t)1ULL);
v___x_3929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3923_, v___x_3927_, v___x_3928_, v_x_3924_, v_x_3925_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_3930_, lean_object* v_val_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v___x_3934_; lean_object* v_mctx_3935_; lean_object* v_cache_3936_; lean_object* v_zetaDeltaFVarIds_3937_; lean_object* v_postponed_3938_; lean_object* v_diag_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3969_; 
v___x_3934_ = lean_st_ref_take(v___y_3932_);
v_mctx_3935_ = lean_ctor_get(v___x_3934_, 0);
v_cache_3936_ = lean_ctor_get(v___x_3934_, 1);
v_zetaDeltaFVarIds_3937_ = lean_ctor_get(v___x_3934_, 2);
v_postponed_3938_ = lean_ctor_get(v___x_3934_, 3);
v_diag_3939_ = lean_ctor_get(v___x_3934_, 4);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3941_ = v___x_3934_;
v_isShared_3942_ = v_isSharedCheck_3969_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_diag_3939_);
lean_inc(v_postponed_3938_);
lean_inc(v_zetaDeltaFVarIds_3937_);
lean_inc(v_cache_3936_);
lean_inc(v_mctx_3935_);
lean_dec(v___x_3934_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3969_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v_depth_3943_; lean_object* v_levelAssignDepth_3944_; lean_object* v_lmvarCounter_3945_; lean_object* v_mvarCounter_3946_; lean_object* v_lDecls_3947_; lean_object* v_decls_3948_; lean_object* v_userNames_3949_; lean_object* v_lAssignment_3950_; lean_object* v_eAssignment_3951_; lean_object* v_dAssignment_3952_; lean_object* v_instanceTypedMVars_3953_; lean_object* v_synthNormMemo_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3968_; 
v_depth_3943_ = lean_ctor_get(v_mctx_3935_, 0);
v_levelAssignDepth_3944_ = lean_ctor_get(v_mctx_3935_, 1);
v_lmvarCounter_3945_ = lean_ctor_get(v_mctx_3935_, 2);
v_mvarCounter_3946_ = lean_ctor_get(v_mctx_3935_, 3);
v_lDecls_3947_ = lean_ctor_get(v_mctx_3935_, 4);
v_decls_3948_ = lean_ctor_get(v_mctx_3935_, 5);
v_userNames_3949_ = lean_ctor_get(v_mctx_3935_, 6);
v_lAssignment_3950_ = lean_ctor_get(v_mctx_3935_, 7);
v_eAssignment_3951_ = lean_ctor_get(v_mctx_3935_, 8);
v_dAssignment_3952_ = lean_ctor_get(v_mctx_3935_, 9);
v_instanceTypedMVars_3953_ = lean_ctor_get(v_mctx_3935_, 10);
v_synthNormMemo_3954_ = lean_ctor_get(v_mctx_3935_, 11);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_mctx_3935_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3956_ = v_mctx_3935_;
v_isShared_3957_ = v_isSharedCheck_3968_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_synthNormMemo_3954_);
lean_inc(v_instanceTypedMVars_3953_);
lean_inc(v_dAssignment_3952_);
lean_inc(v_eAssignment_3951_);
lean_inc(v_lAssignment_3950_);
lean_inc(v_userNames_3949_);
lean_inc(v_decls_3948_);
lean_inc(v_lDecls_3947_);
lean_inc(v_mvarCounter_3946_);
lean_inc(v_lmvarCounter_3945_);
lean_inc(v_levelAssignDepth_3944_);
lean_inc(v_depth_3943_);
lean_dec(v_mctx_3935_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3968_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3958_ = lean_box(0);
v___x_3959_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_3951_, v_mvarId_3930_, v_val_3931_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 8, v___x_3959_);
v___x_3961_ = v___x_3956_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_depth_3943_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_levelAssignDepth_3944_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_lmvarCounter_3945_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_mvarCounter_3946_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_lDecls_3947_);
lean_ctor_set(v_reuseFailAlloc_3967_, 5, v_decls_3948_);
lean_ctor_set(v_reuseFailAlloc_3967_, 6, v_userNames_3949_);
lean_ctor_set(v_reuseFailAlloc_3967_, 7, v_lAssignment_3950_);
lean_ctor_set(v_reuseFailAlloc_3967_, 8, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3967_, 9, v_dAssignment_3952_);
lean_ctor_set(v_reuseFailAlloc_3967_, 10, v_instanceTypedMVars_3953_);
lean_ctor_set(v_reuseFailAlloc_3967_, 11, v_synthNormMemo_3954_);
v___x_3961_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3963_; 
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3961_);
v___x_3963_ = v___x_3941_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_cache_3936_);
lean_ctor_set(v_reuseFailAlloc_3966_, 2, v_zetaDeltaFVarIds_3937_);
lean_ctor_set(v_reuseFailAlloc_3966_, 3, v_postponed_3938_);
lean_ctor_set(v_reuseFailAlloc_3966_, 4, v_diag_3939_);
v___x_3963_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = lean_st_ref_put(v___y_3932_, v___x_3963_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3958_);
return v___x_3965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_3970_, lean_object* v_val_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_3970_, v_val_3971_, v___y_3972_);
lean_dec(v___y_3972_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_3975_, size_t v_i_3976_, lean_object* v_bs_3977_){
_start:
{
uint8_t v___x_3978_; 
v___x_3978_ = lean_usize_dec_lt(v_i_3976_, v_sz_3975_);
if (v___x_3978_ == 0)
{
return v_bs_3977_;
}
else
{
lean_object* v_v_3979_; lean_object* v___x_3980_; lean_object* v_bs_x27_3981_; lean_object* v___x_3982_; size_t v___x_3983_; size_t v___x_3984_; lean_object* v___x_3985_; 
v_v_3979_ = lean_array_uget(v_bs_3977_, v_i_3976_);
v___x_3980_ = lean_unsigned_to_nat(0u);
v_bs_x27_3981_ = lean_array_uset(v_bs_3977_, v_i_3976_, v___x_3980_);
v___x_3982_ = l_Lean_Expr_fvar___override(v_v_3979_);
v___x_3983_ = ((size_t)1ULL);
v___x_3984_ = lean_usize_add(v_i_3976_, v___x_3983_);
v___x_3985_ = lean_array_uset(v_bs_x27_3981_, v_i_3976_, v___x_3982_);
v_i_3976_ = v___x_3984_;
v_bs_3977_ = v___x_3985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_3987_, lean_object* v_i_3988_, lean_object* v_bs_3989_){
_start:
{
size_t v_sz_boxed_3990_; size_t v_i_boxed_3991_; lean_object* v_res_3992_; 
v_sz_boxed_3990_ = lean_unbox_usize(v_sz_3987_);
lean_dec(v_sz_3987_);
v_i_boxed_3991_ = lean_unbox_usize(v_i_3988_);
lean_dec(v_i_3988_);
v_res_3992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_3990_, v_i_boxed_3991_, v_bs_3989_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_3993_, lean_object* v_mvarId_3994_, lean_object* v_a_3995_, lean_object* v___x_3996_, lean_object* v_fvarIds_3997_, lean_object* v_es_3998_, lean_object* v_givenNames_x27_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4006_ = lean_array_get_borrowed(v___x_3993_, v_es_3998_, v___x_4005_);
v___x_4056_ = lean_array_get_size(v_fvarIds_3997_);
v___x_4057_ = lean_nat_dec_eq(v___x_4056_, v___x_4005_);
if (v___x_4057_ == 0)
{
lean_dec(v___x_3996_);
goto v___jp_4007_;
}
else
{
uint8_t v___x_4058_; 
v___x_4058_ = lean_expr_eqv(v_a_3995_, v___x_4006_);
if (v___x_4058_ == 0)
{
lean_dec(v___x_3996_);
goto v___jp_4007_;
}
else
{
lean_object* v___x_4059_; 
lean_inc(v_mvarId_3994_);
v___x_4059_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_3996_, v_mvarId_3994_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_dec_ref_known(v___x_4059_, 1);
goto v___jp_4007_;
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec(v_givenNames_x27_3999_);
lean_dec_ref(v_fvarIds_3997_);
lean_dec(v_mvarId_3994_);
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
v___jp_4007_:
{
lean_object* v___x_4008_; 
lean_inc(v_mvarId_3994_);
v___x_4008_ = l_Lean_MVarId_getTag(v_mvarId_3994_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
lean_inc(v___x_4006_);
v___x_4010_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4006_, v_a_4009_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; size_t v_sz_4012_; size_t v___x_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; uint8_t v___x_4016_; uint8_t v___x_4017_; lean_object* v___x_4018_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc_n(v_a_4011_, 2);
lean_dec_ref_known(v___x_4010_, 1);
v_sz_4012_ = lean_array_size(v_fvarIds_3997_);
v___x_4013_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_3997_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4012_, v___x_4013_, v_fvarIds_3997_);
v___x_4015_ = 0;
v___x_4016_ = 1;
v___x_4017_ = 1;
v___x_4018_ = l_Lean_Meta_mkLetFVars(v___x_4014_, v_a_4011_, v___x_4015_, v___x_4016_, v___x_4017_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec_ref(v___x_4014_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4030_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref_known(v___x_4018_, 1);
v___x_4020_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_3994_, v_a_4019_, v___y_4001_);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4030_ == 0)
{
lean_object* v_unused_4031_; 
v_unused_4031_ = lean_ctor_get(v___x_4020_, 0);
lean_dec(v_unused_4031_);
v___x_4022_ = v___x_4020_;
v_isShared_4023_ = v_isSharedCheck_4030_;
goto v_resetjp_4021_;
}
else
{
lean_dec(v___x_4020_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4030_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4024_, 0, v_fvarIds_3997_);
lean_ctor_set(v___x_4024_, 1, v_givenNames_x27_3999_);
v___x_4025_ = l_Lean_Expr_mvarId_x21(v_a_4011_);
lean_dec(v_a_4011_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4026_);
v___x_4028_ = v___x_4022_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec(v_a_4011_);
lean_dec(v_givenNames_x27_3999_);
lean_dec_ref(v_fvarIds_3997_);
lean_dec(v_mvarId_3994_);
v_a_4032_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4018_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4018_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_dec(v_givenNames_x27_3999_);
lean_dec_ref(v_fvarIds_3997_);
lean_dec(v_mvarId_3994_);
v_a_4040_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4010_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4010_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v_givenNames_x27_3999_);
lean_dec_ref(v_fvarIds_3997_);
lean_dec(v_mvarId_3994_);
v_a_4048_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4008_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4008_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4068_, lean_object* v_mvarId_4069_, lean_object* v_a_4070_, lean_object* v___x_4071_, lean_object* v_fvarIds_4072_, lean_object* v_es_4073_, lean_object* v_givenNames_x27_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_Lean_MVarId_extractLets___lam__0(v___x_4068_, v_mvarId_4069_, v_a_4070_, v___x_4071_, v_fvarIds_4072_, v_es_4073_, v_givenNames_x27_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec_ref(v_es_4073_);
lean_dec_ref(v_a_4070_);
lean_dec_ref(v___x_4068_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4081_, lean_object* v___x_4082_, lean_object* v___x_4083_, lean_object* v_givenNames_4084_, lean_object* v_config_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
lean_inc(v___x_4082_);
lean_inc(v_mvarId_4081_);
v___x_4091_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4081_, v___x_4082_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v___x_4092_; 
lean_dec_ref_known(v___x_4091_, 1);
lean_inc(v_mvarId_4081_);
v___x_4092_ = l_Lean_MVarId_getType(v_mvarId_4081_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___f_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc_n(v_a_4093_, 2);
lean_dec_ref_known(v___x_4092_, 1);
v___f_4094_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4094_, 0, v___x_4083_);
lean_closure_set(v___f_4094_, 1, v_mvarId_4081_);
lean_closure_set(v___f_4094_, 2, v_a_4093_);
lean_closure_set(v___f_4094_, 3, v___x_4082_);
v___x_4095_ = lean_unsigned_to_nat(1u);
v___x_4096_ = lean_mk_empty_array_with_capacity(v___x_4095_);
v___x_4097_ = lean_array_push(v___x_4096_, v_a_4093_);
v___x_4098_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4097_, v_givenNames_4084_, v___f_4094_, v_config_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4098_;
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_givenNames_4084_);
lean_dec_ref(v___x_4083_);
lean_dec(v___x_4082_);
lean_dec(v_mvarId_4081_);
v_a_4099_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4092_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4092_);
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
lean_dec(v_givenNames_4084_);
lean_dec_ref(v___x_4083_);
lean_dec(v___x_4082_);
lean_dec(v_mvarId_4081_);
v_a_4107_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4091_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4091_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4115_, lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v_givenNames_4118_, lean_object* v_config_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4115_, v___x_4116_, v___x_4117_, v_givenNames_4118_, v_config_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec_ref(v_config_4119_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4129_, lean_object* v_givenNames_4130_, lean_object* v_config_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___f_4139_; lean_object* v___x_4140_; 
v___x_4137_ = l_Lean_instInhabitedExpr;
v___x_4138_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4129_);
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4139_, 0, v_mvarId_4129_);
lean_closure_set(v___f_4139_, 1, v___x_4138_);
lean_closure_set(v___f_4139_, 2, v___x_4137_);
lean_closure_set(v___f_4139_, 3, v_givenNames_4130_);
lean_closure_set(v___f_4139_, 4, v_config_4131_);
v___x_4140_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4129_, v___f_4139_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4141_, lean_object* v_givenNames_4142_, lean_object* v_config_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_MVarId_extractLets(v_mvarId_4141_, v_givenNames_4142_, v_config_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4150_, lean_object* v_val_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4150_, v_val_4151_, v___y_4153_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4158_, lean_object* v_val_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4158_, v_val_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4166_, lean_object* v_x_4167_, lean_object* v_x_4168_, lean_object* v_x_4169_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4167_, v_x_4168_, v_x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4171_, lean_object* v_x_4172_, size_t v_x_4173_, size_t v_x_4174_, lean_object* v_x_4175_, lean_object* v_x_4176_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4172_, v_x_4173_, v_x_4174_, v_x_4175_, v_x_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4178_, lean_object* v_x_4179_, lean_object* v_x_4180_, lean_object* v_x_4181_, lean_object* v_x_4182_, lean_object* v_x_4183_){
_start:
{
size_t v_x_2792__boxed_4184_; size_t v_x_2793__boxed_4185_; lean_object* v_res_4186_; 
v_x_2792__boxed_4184_ = lean_unbox_usize(v_x_4180_);
lean_dec(v_x_4180_);
v_x_2793__boxed_4185_ = lean_unbox_usize(v_x_4181_);
lean_dec(v_x_4181_);
v_res_4186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4178_, v_x_4179_, v_x_2792__boxed_4184_, v_x_2793__boxed_4185_, v_x_4182_, v_x_4183_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4187_, lean_object* v_n_4188_, lean_object* v_k_4189_, lean_object* v_v_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4188_, v_k_4189_, v_v_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4192_, size_t v_depth_4193_, lean_object* v_keys_4194_, lean_object* v_vals_4195_, lean_object* v_heq_4196_, lean_object* v_i_4197_, lean_object* v_entries_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4193_, v_keys_4194_, v_vals_4195_, v_i_4197_, v_entries_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4200_, lean_object* v_depth_4201_, lean_object* v_keys_4202_, lean_object* v_vals_4203_, lean_object* v_heq_4204_, lean_object* v_i_4205_, lean_object* v_entries_4206_){
_start:
{
size_t v_depth_boxed_4207_; lean_object* v_res_4208_; 
v_depth_boxed_4207_ = lean_unbox_usize(v_depth_4201_);
lean_dec(v_depth_4201_);
v_res_4208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4200_, v_depth_boxed_4207_, v_keys_4202_, v_vals_4203_, v_heq_4204_, v_i_4205_, v_entries_4206_);
lean_dec_ref(v_vals_4203_);
lean_dec_ref(v_keys_4202_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4209_, lean_object* v_x_4210_, lean_object* v_x_4211_, lean_object* v_x_4212_, lean_object* v_x_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4210_, v_x_4211_, v_x_4212_, v_x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4215_, size_t v_i_4216_, lean_object* v_bs_4217_){
_start:
{
uint8_t v___x_4218_; 
v___x_4218_ = lean_usize_dec_lt(v_i_4216_, v_sz_4215_);
if (v___x_4218_ == 0)
{
return v_bs_4217_;
}
else
{
lean_object* v_v_4219_; lean_object* v___x_4220_; lean_object* v_bs_x27_4221_; lean_object* v___x_4222_; size_t v___x_4223_; size_t v___x_4224_; lean_object* v___x_4225_; 
v_v_4219_ = lean_array_uget(v_bs_4217_, v_i_4216_);
v___x_4220_ = lean_unsigned_to_nat(0u);
v_bs_x27_4221_ = lean_array_uset(v_bs_4217_, v_i_4216_, v___x_4220_);
v___x_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4222_, 0, v_v_4219_);
v___x_4223_ = ((size_t)1ULL);
v___x_4224_ = lean_usize_add(v_i_4216_, v___x_4223_);
v___x_4225_ = lean_array_uset(v_bs_x27_4221_, v_i_4216_, v___x_4222_);
v_i_4216_ = v___x_4224_;
v_bs_4217_ = v___x_4225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4227_, lean_object* v_i_4228_, lean_object* v_bs_4229_){
_start:
{
size_t v_sz_boxed_4230_; size_t v_i_boxed_4231_; lean_object* v_res_4232_; 
v_sz_boxed_4230_ = lean_unbox_usize(v_sz_4227_);
lean_dec(v_sz_4227_);
v_i_boxed_4231_ = lean_unbox_usize(v_i_4228_);
lean_dec(v_i_4228_);
v_res_4232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4230_, v_i_boxed_4231_, v_bs_4229_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4233_, lean_object* v_fvars_4234_, lean_object* v_fvarIds_4235_, lean_object* v_givenNames_x27_4236_, lean_object* v_targetNew_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; 
lean_inc(v_mvarId_4233_);
v___x_4243_ = l_Lean_MVarId_getTag(v_mvarId_4233_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4245_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
v___x_4245_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4237_, v_a_4244_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; size_t v_sz_4247_; size_t v___x_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; uint8_t v___x_4251_; uint8_t v___x_4252_; lean_object* v___x_4253_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc_n(v_a_4246_, 2);
lean_dec_ref_known(v___x_4245_, 1);
v_sz_4247_ = lean_array_size(v_fvarIds_4235_);
v___x_4248_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4235_);
v___x_4249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4247_, v___x_4248_, v_fvarIds_4235_);
v___x_4250_ = 0;
v___x_4251_ = 1;
v___x_4252_ = 1;
v___x_4253_ = l_Lean_Meta_mkLetFVars(v___x_4249_, v_a_4246_, v___x_4250_, v___x_4251_, v___x_4252_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec_ref(v___x_4249_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4268_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4233_, v_a_4254_, v___y_4239_);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4268_ == 0)
{
lean_object* v_unused_4269_; 
v_unused_4269_ = lean_ctor_get(v___x_4255_, 0);
lean_dec(v_unused_4269_);
v___x_4257_ = v___x_4255_;
v_isShared_4258_ = v_isSharedCheck_4268_;
goto v_resetjp_4256_;
}
else
{
lean_dec(v___x_4255_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4268_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; size_t v_sz_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
v___x_4259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4259_, 0, v_fvarIds_4235_);
lean_ctor_set(v___x_4259_, 1, v_givenNames_x27_4236_);
v_sz_4260_ = lean_array_size(v_fvars_4234_);
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4260_, v___x_4248_, v_fvars_4234_);
v___x_4262_ = l_Lean_Expr_mvarId_x21(v_a_4246_);
lean_dec(v_a_4246_);
v___x_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4261_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4259_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4264_);
v___x_4266_ = v___x_4257_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec(v_a_4246_);
lean_dec(v_givenNames_x27_4236_);
lean_dec_ref(v_fvarIds_4235_);
lean_dec_ref(v_fvars_4234_);
lean_dec(v_mvarId_4233_);
v_a_4270_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4253_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4253_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec(v_givenNames_x27_4236_);
lean_dec_ref(v_fvarIds_4235_);
lean_dec_ref(v_fvars_4234_);
lean_dec(v_mvarId_4233_);
v_a_4278_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4245_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4245_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_dec_ref(v_targetNew_4237_);
lean_dec(v_givenNames_x27_4236_);
lean_dec_ref(v_fvarIds_4235_);
lean_dec_ref(v_fvars_4234_);
lean_dec(v_mvarId_4233_);
v_a_4286_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4243_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4243_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4294_, lean_object* v_fvars_4295_, lean_object* v_fvarIds_4296_, lean_object* v_givenNames_x27_4297_, lean_object* v_targetNew_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4294_, v_fvars_4295_, v_fvarIds_4296_, v_givenNames_x27_4297_, v_targetNew_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4305_, lean_object* v_binderName_4306_, lean_object* v_body_4307_, uint8_t v_binderInfo_4308_, lean_object* v___f_4309_, lean_object* v_binderType_4310_, lean_object* v___x_4311_, lean_object* v_mvarId_4312_, lean_object* v_fvarIds_4313_, lean_object* v_es_4314_, lean_object* v_givenNames_x27_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4326_; uint8_t v___x_4327_; 
v___x_4321_ = lean_unsigned_to_nat(0u);
v___x_4322_ = lean_array_get_borrowed(v___x_4305_, v_es_4314_, v___x_4321_);
v___x_4326_ = lean_array_get_size(v_fvarIds_4313_);
v___x_4327_ = lean_nat_dec_eq(v___x_4326_, v___x_4321_);
if (v___x_4327_ == 0)
{
lean_dec(v_mvarId_4312_);
lean_dec(v___x_4311_);
goto v___jp_4323_;
}
else
{
uint8_t v___x_4328_; 
v___x_4328_ = lean_expr_eqv(v_binderType_4310_, v___x_4322_);
if (v___x_4328_ == 0)
{
lean_dec(v_mvarId_4312_);
lean_dec(v___x_4311_);
goto v___jp_4323_;
}
else
{
lean_object* v___x_4329_; 
v___x_4329_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4311_, v_mvarId_4312_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_dec_ref_known(v___x_4329_, 1);
goto v___jp_4323_;
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_dec(v_givenNames_x27_4315_);
lean_dec_ref(v_fvarIds_4313_);
lean_dec_ref(v___f_4309_);
lean_dec_ref(v_body_4307_);
lean_dec(v_binderName_4306_);
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4329_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4329_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
}
}
v___jp_4323_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
lean_inc(v___x_4322_);
v___x_4324_ = l_Lean_Expr_forallE___override(v_binderName_4306_, v___x_4322_, v_body_4307_, v_binderInfo_4308_);
lean_inc(v___y_4319_);
lean_inc_ref(v___y_4318_);
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
v___x_4325_ = lean_apply_8(v___f_4309_, v_fvarIds_4313_, v_givenNames_x27_4315_, v___x_4324_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, lean_box(0));
return v___x_4325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4338_, lean_object* v_binderName_4339_, lean_object* v_body_4340_, lean_object* v_binderInfo_4341_, lean_object* v___f_4342_, lean_object* v_binderType_4343_, lean_object* v___x_4344_, lean_object* v_mvarId_4345_, lean_object* v_fvarIds_4346_, lean_object* v_es_4347_, lean_object* v_givenNames_x27_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
uint8_t v_binderInfo_1803__boxed_4354_; lean_object* v_res_4355_; 
v_binderInfo_1803__boxed_4354_ = lean_unbox(v_binderInfo_4341_);
v_res_4355_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4338_, v_binderName_4339_, v_body_4340_, v_binderInfo_1803__boxed_4354_, v___f_4342_, v_binderType_4343_, v___x_4344_, v_mvarId_4345_, v_fvarIds_4346_, v_es_4347_, v_givenNames_x27_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v_es_4347_);
lean_dec_ref(v_binderType_4343_);
lean_dec_ref(v___x_4338_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4356_, lean_object* v_declName_4357_, lean_object* v_body_4358_, uint8_t v_nondep_4359_, lean_object* v___f_4360_, lean_object* v_type_4361_, lean_object* v_value_4362_, lean_object* v___x_4363_, lean_object* v_mvarId_4364_, lean_object* v_fvarIds_4365_, lean_object* v_es_4366_, lean_object* v_givenNames_x27_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4373_ = lean_unsigned_to_nat(0u);
v___x_4374_ = lean_array_get_borrowed(v___x_4356_, v_es_4366_, v___x_4373_);
v___x_4375_ = lean_unsigned_to_nat(1u);
v___x_4376_ = lean_array_get_borrowed(v___x_4356_, v_es_4366_, v___x_4375_);
v___x_4380_ = lean_array_get_size(v_fvarIds_4365_);
v___x_4381_ = lean_nat_dec_eq(v___x_4380_, v___x_4373_);
if (v___x_4381_ == 0)
{
lean_dec(v_mvarId_4364_);
lean_dec(v___x_4363_);
goto v___jp_4377_;
}
else
{
uint8_t v___x_4382_; 
v___x_4382_ = lean_expr_eqv(v_type_4361_, v___x_4374_);
if (v___x_4382_ == 0)
{
lean_dec(v_mvarId_4364_);
lean_dec(v___x_4363_);
goto v___jp_4377_;
}
else
{
uint8_t v___x_4383_; 
v___x_4383_ = lean_expr_eqv(v_value_4362_, v___x_4376_);
if (v___x_4383_ == 0)
{
lean_dec(v_mvarId_4364_);
lean_dec(v___x_4363_);
goto v___jp_4377_;
}
else
{
lean_object* v___x_4384_; 
v___x_4384_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4363_, v_mvarId_4364_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_dec_ref_known(v___x_4384_, 1);
goto v___jp_4377_;
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_givenNames_x27_4367_);
lean_dec_ref(v_fvarIds_4365_);
lean_dec_ref(v___f_4360_);
lean_dec_ref(v_body_4358_);
lean_dec(v_declName_4357_);
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4384_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4384_);
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
}
}
v___jp_4377_:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_inc(v___x_4376_);
lean_inc(v___x_4374_);
v___x_4378_ = l_Lean_Expr_letE___override(v_declName_4357_, v___x_4374_, v___x_4376_, v_body_4358_, v_nondep_4359_);
lean_inc(v___y_4371_);
lean_inc_ref(v___y_4370_);
lean_inc(v___y_4369_);
lean_inc_ref(v___y_4368_);
v___x_4379_ = lean_apply_8(v___f_4360_, v_fvarIds_4365_, v_givenNames_x27_4367_, v___x_4378_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, lean_box(0));
return v___x_4379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4393_ = _args[0];
lean_object* v_declName_4394_ = _args[1];
lean_object* v_body_4395_ = _args[2];
lean_object* v_nondep_4396_ = _args[3];
lean_object* v___f_4397_ = _args[4];
lean_object* v_type_4398_ = _args[5];
lean_object* v_value_4399_ = _args[6];
lean_object* v___x_4400_ = _args[7];
lean_object* v_mvarId_4401_ = _args[8];
lean_object* v_fvarIds_4402_ = _args[9];
lean_object* v_es_4403_ = _args[10];
lean_object* v_givenNames_x27_4404_ = _args[11];
lean_object* v___y_4405_ = _args[12];
lean_object* v___y_4406_ = _args[13];
lean_object* v___y_4407_ = _args[14];
lean_object* v___y_4408_ = _args[15];
lean_object* v___y_4409_ = _args[16];
_start:
{
uint8_t v_nondep_1874__boxed_4410_; lean_object* v_res_4411_; 
v_nondep_1874__boxed_4410_ = lean_unbox(v_nondep_4396_);
v_res_4411_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4393_, v_declName_4394_, v_body_4395_, v_nondep_1874__boxed_4410_, v___f_4397_, v_type_4398_, v_value_4399_, v___x_4400_, v_mvarId_4401_, v_fvarIds_4402_, v_es_4403_, v_givenNames_x27_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec_ref(v_es_4403_);
lean_dec_ref(v_value_4399_);
lean_dec_ref(v_type_4398_);
lean_dec_ref(v___x_4393_);
return v_res_4411_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4416_ = l_Lean_MessageData_ofFormat(v___x_4415_);
return v___x_4416_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4417_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4419_, lean_object* v___x_4420_, lean_object* v___f_4421_, lean_object* v___x_4422_, lean_object* v_givenNames_4423_, lean_object* v_config_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v___x_4430_; 
lean_inc(v_mvarId_4419_);
v___x_4430_ = l_Lean_MVarId_getType(v_mvarId_4419_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4431_);
lean_dec_ref_known(v___x_4430_, 1);
switch(lean_obj_tag(v_a_4431_))
{
case 7:
{
lean_object* v_binderName_4432_; lean_object* v_binderType_4433_; lean_object* v_body_4434_; uint8_t v_binderInfo_4435_; lean_object* v___x_4436_; lean_object* v___f_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v_binderName_4432_ = lean_ctor_get(v_a_4431_, 0);
lean_inc(v_binderName_4432_);
v_binderType_4433_ = lean_ctor_get(v_a_4431_, 1);
lean_inc_ref_n(v_binderType_4433_, 2);
v_body_4434_ = lean_ctor_get(v_a_4431_, 2);
lean_inc_ref(v_body_4434_);
v_binderInfo_4435_ = lean_ctor_get_uint8(v_a_4431_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4431_, 3);
v___x_4436_ = lean_box(v_binderInfo_4435_);
v___f_4437_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4437_, 0, v___x_4420_);
lean_closure_set(v___f_4437_, 1, v_binderName_4432_);
lean_closure_set(v___f_4437_, 2, v_body_4434_);
lean_closure_set(v___f_4437_, 3, v___x_4436_);
lean_closure_set(v___f_4437_, 4, v___f_4421_);
lean_closure_set(v___f_4437_, 5, v_binderType_4433_);
lean_closure_set(v___f_4437_, 6, v___x_4422_);
lean_closure_set(v___f_4437_, 7, v_mvarId_4419_);
v___x_4438_ = lean_unsigned_to_nat(1u);
v___x_4439_ = lean_mk_empty_array_with_capacity(v___x_4438_);
v___x_4440_ = lean_array_push(v___x_4439_, v_binderType_4433_);
v___x_4441_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4440_, v_givenNames_4423_, v___f_4437_, v_config_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
return v___x_4441_;
}
case 8:
{
lean_object* v_declName_4442_; lean_object* v_type_4443_; lean_object* v_value_4444_; lean_object* v_body_4445_; uint8_t v_nondep_4446_; lean_object* v___x_4447_; lean_object* v___f_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v_declName_4442_ = lean_ctor_get(v_a_4431_, 0);
lean_inc(v_declName_4442_);
v_type_4443_ = lean_ctor_get(v_a_4431_, 1);
lean_inc_ref_n(v_type_4443_, 2);
v_value_4444_ = lean_ctor_get(v_a_4431_, 2);
lean_inc_ref_n(v_value_4444_, 2);
v_body_4445_ = lean_ctor_get(v_a_4431_, 3);
lean_inc_ref(v_body_4445_);
v_nondep_4446_ = lean_ctor_get_uint8(v_a_4431_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4431_, 4);
v___x_4447_ = lean_box(v_nondep_4446_);
v___f_4448_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4448_, 0, v___x_4420_);
lean_closure_set(v___f_4448_, 1, v_declName_4442_);
lean_closure_set(v___f_4448_, 2, v_body_4445_);
lean_closure_set(v___f_4448_, 3, v___x_4447_);
lean_closure_set(v___f_4448_, 4, v___f_4421_);
lean_closure_set(v___f_4448_, 5, v_type_4443_);
lean_closure_set(v___f_4448_, 6, v_value_4444_);
lean_closure_set(v___f_4448_, 7, v___x_4422_);
lean_closure_set(v___f_4448_, 8, v_mvarId_4419_);
v___x_4449_ = lean_unsigned_to_nat(2u);
v___x_4450_ = lean_mk_empty_array_with_capacity(v___x_4449_);
v___x_4451_ = lean_array_push(v___x_4450_, v_type_4443_);
v___x_4452_ = lean_array_push(v___x_4451_, v_value_4444_);
v___x_4453_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4452_, v_givenNames_4423_, v___f_4448_, v_config_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
return v___x_4453_;
}
default: 
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_dec(v_a_4431_);
lean_dec(v_givenNames_4423_);
lean_dec_ref(v___f_4421_);
lean_dec_ref(v___x_4420_);
v___x_4454_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4455_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4422_, v_mvarId_4419_, v___x_4454_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
return v___x_4455_;
}
}
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec(v_givenNames_4423_);
lean_dec(v___x_4422_);
lean_dec_ref(v___f_4421_);
lean_dec_ref(v___x_4420_);
lean_dec(v_mvarId_4419_);
v_a_4456_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4430_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4430_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4464_, lean_object* v___x_4465_, lean_object* v___f_4466_, lean_object* v___x_4467_, lean_object* v_givenNames_4468_, lean_object* v_config_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4464_, v___x_4465_, v___f_4466_, v___x_4467_, v_givenNames_4468_, v_config_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec_ref(v_config_4469_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4476_, lean_object* v___x_4477_, lean_object* v_givenNames_4478_, lean_object* v_config_4479_, lean_object* v_mvarId_4480_, lean_object* v_fvars_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v___f_4487_; lean_object* v___f_4488_; lean_object* v___x_4489_; 
lean_inc_n(v_mvarId_4480_, 2);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4487_, 0, v_mvarId_4480_);
lean_closure_set(v___f_4487_, 1, v_fvars_4481_);
v___f_4488_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4488_, 0, v_mvarId_4480_);
lean_closure_set(v___f_4488_, 1, v___x_4476_);
lean_closure_set(v___f_4488_, 2, v___f_4487_);
lean_closure_set(v___f_4488_, 3, v___x_4477_);
lean_closure_set(v___f_4488_, 4, v_givenNames_4478_);
lean_closure_set(v___f_4488_, 5, v_config_4479_);
v___x_4489_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4480_, v___f_4488_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4490_, lean_object* v___x_4491_, lean_object* v_givenNames_4492_, lean_object* v_config_4493_, lean_object* v_mvarId_4494_, lean_object* v_fvars_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4490_, v___x_4491_, v_givenNames_4492_, v_config_4493_, v_mvarId_4494_, v_fvars_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4502_, lean_object* v_fvarId_4503_, lean_object* v_givenNames_4504_, lean_object* v_config_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___f_4513_; lean_object* v___x_4514_; 
v___x_4511_ = l_Lean_instInhabitedExpr;
v___x_4512_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
v___f_4513_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4513_, 0, v___x_4511_);
lean_closure_set(v___f_4513_, 1, v___x_4512_);
lean_closure_set(v___f_4513_, 2, v_givenNames_4504_);
lean_closure_set(v___f_4513_, 3, v_config_4505_);
lean_inc(v_mvarId_4502_);
v___x_4514_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4502_, v___x_4512_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; lean_object* v___x_4519_; 
lean_dec_ref_known(v___x_4514_, 1);
v___x_4515_ = lean_unsigned_to_nat(1u);
v___x_4516_ = lean_mk_empty_array_with_capacity(v___x_4515_);
v___x_4517_ = lean_array_push(v___x_4516_, v_fvarId_4503_);
v___x_4518_ = 0;
v___x_4519_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4502_, v___x_4517_, v___f_4513_, v___x_4518_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
return v___x_4519_;
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
lean_dec_ref(v___f_4513_);
lean_dec(v_fvarId_4503_);
lean_dec(v_mvarId_4502_);
v_a_4520_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4514_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4514_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4528_, lean_object* v_fvarId_4529_, lean_object* v_givenNames_4530_, lean_object* v_config_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4528_, v_fvarId_4529_, v_givenNames_4530_, v_config_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4538_, lean_object* v___x_4539_, lean_object* v_config_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v___x_4546_; 
lean_inc(v___x_4539_);
lean_inc(v_mvarId_4538_);
v___x_4546_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4538_, v___x_4539_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v___x_4547_; 
lean_dec_ref_known(v___x_4546_, 1);
lean_inc(v_mvarId_4538_);
v___x_4547_ = l_Lean_MVarId_getType(v_mvarId_4538_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4549_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc_n(v_a_4548_, 2);
lean_dec_ref_known(v___x_4547_, 1);
v___x_4549_ = l_Lean_Meta_liftLets(v_a_4548_, v_config_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; uint8_t v___x_4551_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v___x_4551_ = lean_expr_eqv(v_a_4548_, v_a_4550_);
lean_dec(v_a_4548_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
lean_dec(v___x_4539_);
v___x_4552_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4538_, v_a_4550_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; 
lean_inc(v_mvarId_4538_);
v___x_4553_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4539_, v_mvarId_4538_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v___x_4554_; 
lean_dec_ref_known(v___x_4553_, 1);
v___x_4554_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4538_, v_a_4550_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
return v___x_4554_;
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4550_);
lean_dec(v_mvarId_4538_);
v_a_4555_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4553_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4553_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_a_4548_);
lean_dec(v___x_4539_);
lean_dec(v_mvarId_4538_);
v_a_4563_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4549_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4549_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v_config_4540_);
lean_dec(v___x_4539_);
lean_dec(v_mvarId_4538_);
v_a_4571_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4547_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4547_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v_config_4540_);
lean_dec(v___x_4539_);
lean_dec(v_mvarId_4538_);
v_a_4579_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4546_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4546_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4587_, lean_object* v___x_4588_, lean_object* v_config_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4587_, v___x_4588_, v_config_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4599_, lean_object* v_config_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4606_; lean_object* v___f_4607_; lean_object* v___x_4608_; 
v___x_4606_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4599_);
v___f_4607_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4607_, 0, v_mvarId_4599_);
lean_closure_set(v___f_4607_, 1, v___x_4606_);
lean_closure_set(v___f_4607_, 2, v_config_4600_);
v___x_4608_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4599_, v___f_4607_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4609_, lean_object* v_config_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l_Lean_MVarId_liftLets(v_mvarId_4609_, v_config_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4617_, lean_object* v_fvars_4618_, lean_object* v_targetNew_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4617_, v_targetNew_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4639_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4628_ = v___x_4625_;
v_isShared_4629_ = v_isSharedCheck_4639_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4625_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4639_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; size_t v_sz_4631_; size_t v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
v___x_4630_ = lean_box(0);
v_sz_4631_ = lean_array_size(v_fvars_4618_);
v___x_4632_ = ((size_t)0ULL);
v___x_4633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4631_, v___x_4632_, v_fvars_4618_);
v___x_4634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
lean_ctor_set(v___x_4634_, 1, v_a_4626_);
v___x_4635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4630_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4635_);
v___x_4637_ = v___x_4628_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v_fvars_4618_);
v_a_4640_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4625_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4625_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4648_, lean_object* v_fvars_4649_, lean_object* v_targetNew_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4648_, v_fvars_4649_, v_targetNew_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4657_, lean_object* v_config_4658_, lean_object* v___f_4659_, lean_object* v___x_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___x_4666_; 
lean_inc(v_mvarId_4657_);
v___x_4666_ = l_Lean_MVarId_getType(v_mvarId_4657_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v___x_4666_, 1);
switch(lean_obj_tag(v_a_4667_))
{
case 7:
{
lean_object* v_binderName_4668_; lean_object* v_binderType_4669_; lean_object* v_body_4670_; uint8_t v_binderInfo_4671_; lean_object* v___x_4672_; 
v_binderName_4668_ = lean_ctor_get(v_a_4667_, 0);
lean_inc(v_binderName_4668_);
v_binderType_4669_ = lean_ctor_get(v_a_4667_, 1);
lean_inc_ref_n(v_binderType_4669_, 2);
v_body_4670_ = lean_ctor_get(v_a_4667_, 2);
lean_inc_ref(v_body_4670_);
v_binderInfo_4671_ = lean_ctor_get_uint8(v_a_4667_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4667_, 3);
v___x_4672_ = l_Lean_Meta_liftLets(v_binderType_4669_, v_config_4658_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; uint8_t v___x_4681_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v___x_4681_ = lean_expr_eqv(v_binderType_4669_, v_a_4673_);
lean_dec_ref(v_binderType_4669_);
if (v___x_4681_ == 0)
{
lean_dec(v___x_4660_);
lean_dec(v_mvarId_4657_);
v___y_4675_ = v___y_4661_;
v___y_4676_ = v___y_4662_;
v___y_4677_ = v___y_4663_;
v___y_4678_ = v___y_4664_;
goto v___jp_4674_;
}
else
{
lean_object* v___x_4682_; 
v___x_4682_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4660_, v_mvarId_4657_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_dec_ref_known(v___x_4682_, 1);
v___y_4675_ = v___y_4661_;
v___y_4676_ = v___y_4662_;
v___y_4677_ = v___y_4663_;
v___y_4678_ = v___y_4664_;
goto v___jp_4674_;
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
lean_dec(v_a_4673_);
lean_dec_ref(v_body_4670_);
lean_dec(v_binderName_4668_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v___f_4659_);
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
v___jp_4674_:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = l_Lean_Expr_forallE___override(v_binderName_4668_, v_a_4673_, v_body_4670_, v_binderInfo_4671_);
v___x_4680_ = lean_apply_6(v___f_4659_, v___x_4679_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, lean_box(0));
return v___x_4680_;
}
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_dec_ref(v_body_4670_);
lean_dec_ref(v_binderType_4669_);
lean_dec(v_binderName_4668_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___x_4660_);
lean_dec_ref(v___f_4659_);
lean_dec(v_mvarId_4657_);
v_a_4691_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4672_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4672_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
case 8:
{
lean_object* v_declName_4699_; lean_object* v_type_4700_; lean_object* v_value_4701_; lean_object* v_body_4702_; uint8_t v_nondep_4703_; lean_object* v___x_4704_; 
v_declName_4699_ = lean_ctor_get(v_a_4667_, 0);
lean_inc(v_declName_4699_);
v_type_4700_ = lean_ctor_get(v_a_4667_, 1);
lean_inc_ref_n(v_type_4700_, 2);
v_value_4701_ = lean_ctor_get(v_a_4667_, 2);
lean_inc_ref(v_value_4701_);
v_body_4702_ = lean_ctor_get(v_a_4667_, 3);
lean_inc_ref(v_body_4702_);
v_nondep_4703_ = lean_ctor_get_uint8(v_a_4667_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4667_, 4);
lean_inc_ref(v_config_4658_);
v___x_4704_ = l_Lean_Meta_liftLets(v_type_4700_, v_config_4658_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; lean_object* v___x_4706_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_a_4705_);
lean_dec_ref_known(v___x_4704_, 1);
lean_inc_ref(v_value_4701_);
v___x_4706_ = l_Lean_Meta_liftLets(v_value_4701_, v_config_4658_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; uint8_t v___x_4715_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4706_, 1);
v___x_4715_ = lean_expr_eqv(v_type_4700_, v_a_4705_);
lean_dec_ref(v_type_4700_);
if (v___x_4715_ == 0)
{
lean_dec_ref(v_value_4701_);
lean_dec(v___x_4660_);
lean_dec(v_mvarId_4657_);
v___y_4709_ = v___y_4661_;
v___y_4710_ = v___y_4662_;
v___y_4711_ = v___y_4663_;
v___y_4712_ = v___y_4664_;
goto v___jp_4708_;
}
else
{
uint8_t v___x_4716_; 
v___x_4716_ = lean_expr_eqv(v_value_4701_, v_a_4707_);
lean_dec_ref(v_value_4701_);
if (v___x_4716_ == 0)
{
lean_dec(v___x_4660_);
lean_dec(v_mvarId_4657_);
v___y_4709_ = v___y_4661_;
v___y_4710_ = v___y_4662_;
v___y_4711_ = v___y_4663_;
v___y_4712_ = v___y_4664_;
goto v___jp_4708_;
}
else
{
lean_object* v___x_4717_; 
v___x_4717_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4660_, v_mvarId_4657_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_dec_ref_known(v___x_4717_, 1);
v___y_4709_ = v___y_4661_;
v___y_4710_ = v___y_4662_;
v___y_4711_ = v___y_4663_;
v___y_4712_ = v___y_4664_;
goto v___jp_4708_;
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec(v_a_4707_);
lean_dec(v_a_4705_);
lean_dec_ref(v_body_4702_);
lean_dec(v_declName_4699_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v___f_4659_);
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4717_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4717_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
v___jp_4708_:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4713_ = l_Lean_Expr_letE___override(v_declName_4699_, v_a_4705_, v_a_4707_, v_body_4702_, v_nondep_4703_);
v___x_4714_ = lean_apply_6(v___f_4659_, v___x_4713_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, lean_box(0));
return v___x_4714_;
}
}
else
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
lean_dec(v_a_4705_);
lean_dec_ref(v_body_4702_);
lean_dec_ref(v_value_4701_);
lean_dec_ref(v_type_4700_);
lean_dec(v_declName_4699_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___x_4660_);
lean_dec_ref(v___f_4659_);
lean_dec(v_mvarId_4657_);
v_a_4726_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4728_ = v___x_4706_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4706_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
lean_dec_ref(v_body_4702_);
lean_dec_ref(v_value_4701_);
lean_dec_ref(v_type_4700_);
lean_dec(v_declName_4699_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___x_4660_);
lean_dec_ref(v___f_4659_);
lean_dec_ref(v_config_4658_);
lean_dec(v_mvarId_4657_);
v_a_4734_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4704_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4704_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
default: 
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
lean_dec(v_a_4667_);
lean_dec_ref(v___f_4659_);
lean_dec_ref(v_config_4658_);
v___x_4742_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4743_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4660_, v_mvarId_4657_, v___x_4742_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
return v___x_4743_;
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___x_4660_);
lean_dec_ref(v___f_4659_);
lean_dec_ref(v_config_4658_);
lean_dec(v_mvarId_4657_);
v_a_4744_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4666_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4666_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4752_, lean_object* v_config_4753_, lean_object* v___f_4754_, lean_object* v___x_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4752_, v_config_4753_, v___f_4754_, v___x_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4762_, lean_object* v___x_4763_, lean_object* v_mvarId_4764_, lean_object* v_fvars_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v___f_4771_; lean_object* v___f_4772_; lean_object* v___x_4773_; 
lean_inc_n(v_mvarId_4764_, 2);
v___f_4771_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4771_, 0, v_mvarId_4764_);
lean_closure_set(v___f_4771_, 1, v_fvars_4765_);
v___f_4772_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4772_, 0, v_mvarId_4764_);
lean_closure_set(v___f_4772_, 1, v_config_4762_);
lean_closure_set(v___f_4772_, 2, v___f_4771_);
lean_closure_set(v___f_4772_, 3, v___x_4763_);
v___x_4773_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4764_, v___f_4772_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4774_, lean_object* v___x_4775_, lean_object* v_mvarId_4776_, lean_object* v_fvars_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4774_, v___x_4775_, v_mvarId_4776_, v_fvars_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4784_, lean_object* v_fvarId_4785_, lean_object* v_config_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v___x_4792_; lean_object* v___f_4793_; lean_object* v___x_4794_; 
v___x_4792_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
v___f_4793_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4793_, 0, v_config_4786_);
lean_closure_set(v___f_4793_, 1, v___x_4792_);
lean_inc(v_mvarId_4784_);
v___x_4794_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4784_, v___x_4792_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; lean_object* v___x_4799_; 
lean_dec_ref_known(v___x_4794_, 1);
v___x_4795_ = lean_unsigned_to_nat(1u);
v___x_4796_ = lean_mk_empty_array_with_capacity(v___x_4795_);
v___x_4797_ = lean_array_push(v___x_4796_, v_fvarId_4785_);
v___x_4798_ = 0;
v___x_4799_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4784_, v___x_4797_, v___f_4793_, v___x_4798_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4808_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v_snd_4804_; lean_object* v___x_4806_; 
v_snd_4804_ = lean_ctor_get(v_a_4800_, 1);
lean_inc(v_snd_4804_);
lean_dec(v_a_4800_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_snd_4804_);
v___x_4806_ = v___x_4802_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_snd_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
v_a_4809_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4799_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4799_);
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
else
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
lean_dec_ref(v___f_4793_);
lean_dec(v_fvarId_4785_);
lean_dec(v_mvarId_4784_);
v_a_4817_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4794_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4794_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4825_, lean_object* v_fvarId_4826_, lean_object* v_config_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4825_, v_fvarId_4826_, v_config_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4834_, lean_object* v___x_4835_, uint8_t v_failIfUnchanged_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v___x_4842_; 
lean_inc(v___x_4835_);
lean_inc(v_mvarId_4834_);
v___x_4842_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4834_, v___x_4835_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v___x_4843_; 
lean_dec_ref_known(v___x_4842_, 1);
lean_inc(v_mvarId_4834_);
v___x_4843_ = l_Lean_MVarId_getType(v_mvarId_4834_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4845_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
lean_inc_n(v_a_4844_, 2);
lean_dec_ref_known(v___x_4843_, 1);
v___x_4845_ = l_Lean_Meta_letToHave(v_a_4844_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4845_) == 0)
{
if (v_failIfUnchanged_4836_ == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4847_; 
lean_dec(v_a_4844_);
lean_dec(v___x_4835_);
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
lean_inc(v_a_4846_);
lean_dec_ref_known(v___x_4845_, 1);
v___x_4847_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4834_, v_a_4846_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
return v___x_4847_;
}
else
{
lean_object* v_a_4848_; uint8_t v___x_4849_; 
v_a_4848_ = lean_ctor_get(v___x_4845_, 0);
lean_inc(v_a_4848_);
lean_dec_ref_known(v___x_4845_, 1);
v___x_4849_ = lean_expr_eqv(v_a_4844_, v_a_4848_);
lean_dec(v_a_4844_);
if (v___x_4849_ == 0)
{
lean_object* v___x_4850_; 
lean_dec(v___x_4835_);
v___x_4850_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4834_, v_a_4848_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
return v___x_4850_;
}
else
{
lean_object* v___x_4851_; 
lean_inc(v_mvarId_4834_);
v___x_4851_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4835_, v_mvarId_4834_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v___x_4852_; 
lean_dec_ref_known(v___x_4851_, 1);
v___x_4852_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4834_, v_a_4848_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
return v___x_4852_;
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec(v_a_4848_);
lean_dec(v_mvarId_4834_);
v_a_4853_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4851_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4851_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
lean_dec(v_a_4844_);
lean_dec(v___x_4835_);
lean_dec(v_mvarId_4834_);
v_a_4861_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4845_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4845_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v___x_4835_);
lean_dec(v_mvarId_4834_);
v_a_4869_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4843_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4843_);
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
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v___x_4835_);
lean_dec(v_mvarId_4834_);
v_a_4877_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4842_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4842_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4885_, lean_object* v___x_4886_, lean_object* v_failIfUnchanged_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4893_; lean_object* v_res_4894_; 
v_failIfUnchanged_boxed_4893_ = lean_unbox(v_failIfUnchanged_4887_);
v_res_4894_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4885_, v___x_4886_, v_failIfUnchanged_boxed_4893_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec(v___y_4889_);
lean_dec_ref(v___y_4888_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4898_, uint8_t v_failIfUnchanged_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___f_4907_; lean_object* v___x_4908_; 
v___x_4905_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4906_ = lean_box(v_failIfUnchanged_4899_);
lean_inc(v_mvarId_4898_);
v___f_4907_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4907_, 0, v_mvarId_4898_);
lean_closure_set(v___f_4907_, 1, v___x_4905_);
lean_closure_set(v___f_4907_, 2, v___x_4906_);
v___x_4908_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4898_, v___f_4907_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4909_, lean_object* v_failIfUnchanged_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4916_; lean_object* v_res_4917_; 
v_failIfUnchanged_boxed_4916_ = lean_unbox(v_failIfUnchanged_4910_);
v_res_4917_ = l_Lean_MVarId_letToHave(v_mvarId_4909_, v_failIfUnchanged_boxed_4916_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4918_, lean_object* v___x_4919_, lean_object* v_fvarId_4920_, uint8_t v_failIfUnchanged_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v___x_4927_; 
lean_inc(v___x_4919_);
lean_inc(v_mvarId_4918_);
v___x_4927_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4918_, v___x_4919_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v___x_4928_; 
lean_dec_ref_known(v___x_4927_, 1);
lean_inc(v_fvarId_4920_);
v___x_4928_ = l_Lean_FVarId_getType___redArg(v_fvarId_4920_, v___y_4922_, v___y_4924_, v___y_4925_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc_n(v_a_4929_, 2);
lean_dec_ref_known(v___x_4928_, 1);
v___x_4930_ = l_Lean_Meta_letToHave(v_a_4929_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
if (lean_obj_tag(v___x_4930_) == 0)
{
if (v_failIfUnchanged_4921_ == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; 
lean_dec(v_a_4929_);
lean_dec(v___x_4919_);
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4918_, v_fvarId_4920_, v_a_4931_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
return v___x_4932_;
}
else
{
lean_object* v_a_4933_; uint8_t v___x_4934_; 
v_a_4933_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4934_ = lean_expr_eqv(v_a_4929_, v_a_4933_);
lean_dec(v_a_4929_);
if (v___x_4934_ == 0)
{
lean_object* v___x_4935_; 
lean_dec(v___x_4919_);
v___x_4935_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4918_, v_fvarId_4920_, v_a_4933_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
return v___x_4935_;
}
else
{
lean_object* v___x_4936_; 
lean_inc(v_mvarId_4918_);
v___x_4936_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4919_, v_mvarId_4918_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v___x_4937_; 
lean_dec_ref_known(v___x_4936_, 1);
v___x_4937_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4918_, v_fvarId_4920_, v_a_4933_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
return v___x_4937_;
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec(v_a_4933_);
lean_dec(v_fvarId_4920_);
lean_dec(v_mvarId_4918_);
v_a_4938_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4936_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4936_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
lean_dec(v_a_4929_);
lean_dec(v_fvarId_4920_);
lean_dec(v___x_4919_);
lean_dec(v_mvarId_4918_);
v_a_4946_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4930_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4930_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec(v_fvarId_4920_);
lean_dec(v___x_4919_);
lean_dec(v_mvarId_4918_);
v_a_4954_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4928_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4928_);
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
else
{
lean_object* v_a_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4969_; 
lean_dec(v_fvarId_4920_);
lean_dec(v___x_4919_);
lean_dec(v_mvarId_4918_);
v_a_4962_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4964_ = v___x_4927_;
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_a_4962_);
lean_dec(v___x_4927_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_4970_, lean_object* v___x_4971_, lean_object* v_fvarId_4972_, lean_object* v_failIfUnchanged_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4979_; lean_object* v_res_4980_; 
v_failIfUnchanged_boxed_4979_ = lean_unbox(v_failIfUnchanged_4973_);
v_res_4980_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_4970_, v___x_4971_, v_fvarId_4972_, v_failIfUnchanged_boxed_4979_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_4981_, lean_object* v_fvarId_4982_, uint8_t v_failIfUnchanged_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___f_4991_; lean_object* v___x_4992_; 
v___x_4989_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4990_ = lean_box(v_failIfUnchanged_4983_);
lean_inc(v_mvarId_4981_);
v___f_4991_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4991_, 0, v_mvarId_4981_);
lean_closure_set(v___f_4991_, 1, v___x_4989_);
lean_closure_set(v___f_4991_, 2, v_fvarId_4982_);
lean_closure_set(v___f_4991_, 3, v___x_4990_);
v___x_4992_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4981_, v___f_4991_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_4993_, lean_object* v_fvarId_4994_, lean_object* v_failIfUnchanged_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5001_; lean_object* v_res_5002_; 
v_failIfUnchanged_boxed_5001_ = lean_unbox(v_failIfUnchanged_4995_);
v_res_5002_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_4993_, v_fvarId_4994_, v_failIfUnchanged_boxed_5001_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
return v_res_5002_;
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
