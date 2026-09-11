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
lean_object* v_snd_610_; lean_object* v_fst_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_645_; 
v_snd_610_ = lean_ctor_get(v_b_601_, 1);
v_fst_611_ = lean_ctor_get(v_b_601_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v_b_601_);
if (v_isSharedCheck_645_ == 0)
{
v___x_613_ = v_b_601_;
v_isShared_614_ = v_isSharedCheck_645_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_610_);
lean_inc(v_fst_611_);
lean_dec(v_b_601_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_645_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_644_; 
v_fst_615_ = lean_ctor_get(v_snd_610_, 0);
v_snd_616_ = lean_ctor_get(v_snd_610_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_snd_610_);
if (v_isSharedCheck_644_ == 0)
{
v___x_618_ = v_snd_610_;
v_isShared_619_ = v_isSharedCheck_644_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_snd_610_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_644_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_a_620_; lean_object* v_decl_621_; uint8_t v___y_623_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_a_620_ = lean_array_uget_borrowed(v_as_598_, v_i_600_);
v_decl_621_ = lean_ctor_get(v_a_620_, 0);
v___x_640_ = l_Lean_LocalDecl_type(v_decl_621_);
v___x_641_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_611_, v___x_640_);
lean_dec_ref(v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = l_Lean_LocalDecl_value(v_decl_621_, v___x_641_);
v___x_643_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_611_, v___x_642_);
lean_dec_ref(v___x_642_);
v___y_623_ = v___x_643_;
goto v___jp_622_;
}
else
{
v___y_623_ = v___x_641_;
goto v___jp_622_;
}
v___jp_622_:
{
if (v___y_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_626_; 
lean_inc(v_a_620_);
v___x_624_ = lean_array_push(v_fst_615_, v_a_620_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_624_);
v___x_626_ = v___x_618_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_snd_616_);
v___x_626_ = v_reuseFailAlloc_630_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_626_);
v___x_628_ = v___x_613_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_fst_611_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_a_604_ = v___x_628_;
goto v___jp_603_;
}
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
lean_inc(v_a_620_);
v___x_631_ = lean_array_push(v_snd_616_, v_a_620_);
v___x_632_ = l_Lean_LocalDecl_fvarId(v_decl_621_);
v___x_633_ = l_Lean_FVarIdSet_insert(v_fst_611_, v___x_632_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_631_);
v___x_635_ = v___x_618_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_fst_615_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_631_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_635_);
lean_ctor_set(v___x_613_, 0, v___x_633_);
v___x_637_ = v___x_613_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v_a_604_ = v___x_637_;
goto v___jp_603_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(lean_object* v_as_646_, lean_object* v_sz_647_, lean_object* v_i_648_, lean_object* v_b_649_, lean_object* v___y_650_){
_start:
{
size_t v_sz_boxed_651_; size_t v_i_boxed_652_; lean_object* v_res_653_; 
v_sz_boxed_651_ = lean_unbox_usize(v_sz_647_);
lean_dec(v_sz_647_);
v_i_boxed_652_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_646_, v_sz_boxed_651_, v_i_boxed_652_, v_b_649_);
lean_dec_ref(v_as_646_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object* v_fvar_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_fvarSet_665_; lean_object* v_fvarSet_666_; lean_object* v___x_667_; lean_object* v_decls_668_; lean_object* v___x_669_; lean_object* v___x_670_; size_t v_sz_671_; size_t v___x_672_; lean_object* v___x_673_; 
v_fvarSet_665_ = lean_box(1);
v_fvarSet_666_ = l_Lean_FVarIdSet_insert(v_fvarSet_665_, v_fvar_656_);
v___x_667_ = lean_st_ref_get(v_a_659_);
v_decls_668_ = lean_ctor_get(v___x_667_, 1);
lean_inc_ref(v_decls_668_);
lean_dec(v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_fvarSet_666_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v_sz_671_ = lean_array_size(v_decls_668_);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_decls_668_, v_sz_671_, v___x_672_, v___x_670_);
lean_dec_ref(v_decls_668_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_696_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_696_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_696_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_696_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_snd_678_; lean_object* v_fst_679_; lean_object* v_snd_680_; lean_object* v___x_681_; lean_object* v_givenNames_682_; lean_object* v_valueMap_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_694_; 
v_snd_678_ = lean_ctor_get(v_a_674_, 1);
lean_inc(v_snd_678_);
lean_dec(v_a_674_);
v_fst_679_ = lean_ctor_get(v_snd_678_, 0);
lean_inc(v_fst_679_);
v_snd_680_ = lean_ctor_get(v_snd_678_, 1);
lean_inc(v_snd_680_);
lean_dec(v_snd_678_);
v___x_681_ = lean_st_ref_take(v_a_659_);
v_givenNames_682_ = lean_ctor_get(v___x_681_, 0);
v_valueMap_683_ = lean_ctor_get(v___x_681_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_681_, 1);
lean_dec(v_unused_695_);
v___x_685_ = v___x_681_;
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_valueMap_683_);
lean_inc(v_givenNames_682_);
lean_dec(v___x_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_fst_679_);
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_givenNames_682_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_fst_679_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_valueMap_683_);
v___x_688_ = v_reuseFailAlloc_693_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_st_ref_put(v_a_659_, v___x_688_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v_snd_680_);
v___x_691_ = v___x_676_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_snd_680_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_697_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_673_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_673_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object* v_fvar_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Meta_ExtractLets_flushDecls(v_fvar_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_714_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object* v_00_u03b2_715_, lean_object* v_k_716_, lean_object* v_t_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_716_, v_t_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object* v_00_u03b2_719_, lean_object* v_k_720_, lean_object* v_t_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(v_00_u03b2_719_, v_k_720_, v_t_721_);
lean_dec(v_t_721_);
lean_dec(v_k_720_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object* v_as_724_, size_t v_sz_725_, size_t v_i_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_724_, v_sz_725_, v_i_726_, v_b_727_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object* v_as_737_, lean_object* v_sz_738_, lean_object* v_i_739_, lean_object* v_b_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v_sz_boxed_749_ = lean_unbox_usize(v_sz_738_);
lean_dec(v_sz_738_);
v_i_boxed_750_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_737_, v_sz_boxed_749_, v_i_boxed_750_, v_b_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v_as_737_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object* v_x_752_){
_start:
{
lean_object* v_decl_753_; 
v_decl_753_ = lean_ctor_get(v_x_752_, 0);
lean_inc_ref(v_decl_753_);
return v_decl_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object* v_x_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(v_x_754_);
lean_dec_ref(v_x_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object* v_lctx_756_, lean_object* v_x1_757_, lean_object* v_x2_758_){
_start:
{
lean_object* v_decl_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_decl_759_ = lean_ctor_get(v_x2_758_, 0);
v___x_760_ = l_Lean_LocalDecl_fvarId(v_decl_759_);
v___x_761_ = l_Lean_LocalContext_contains(v_lctx_756_, v___x_760_);
lean_dec(v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_array_push(v_x1_757_, v_x2_758_);
return v___x_762_;
}
else
{
lean_dec_ref(v_x2_758_);
return v_x1_757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object* v_lctx_763_, lean_object* v_x1_764_, lean_object* v_x2_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(v_lctx_763_, v_x1_764_, v_x2_765_);
lean_dec_ref(v_lctx_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_k_789_, lean_object* v_decls_790_, lean_object* v_lctx_791_){
_start:
{
lean_object* v___y_793_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_decls_790_);
v___x_802_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_803_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_804_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_804_ == 0)
{
lean_dec_ref(v_lctx_791_);
lean_dec_ref(v_decls_790_);
v___y_793_ = v___x_802_;
goto v___jp_792_;
}
else
{
lean_object* v___f_805_; uint8_t v___x_806_; 
v___f_805_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_805_, 0, v_lctx_791_);
v___x_806_ = lean_nat_dec_le(v___x_801_, v___x_801_);
if (v___x_806_ == 0)
{
if (v___x_804_ == 0)
{
lean_dec_ref(v___f_805_);
lean_dec_ref(v_decls_790_);
v___y_793_ = v___x_802_;
goto v___jp_792_;
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_801_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_803_, v___f_805_, v_decls_790_, v___x_807_, v___x_808_, v___x_802_);
v___y_793_ = v___x_809_;
goto v___jp_792_;
}
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_801_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_803_, v___f_805_, v_decls_790_, v___x_810_, v___x_811_, v___x_802_);
v___y_793_ = v___x_812_;
goto v___jp_792_;
}
}
v___jp_792_:
{
lean_object* v___x_794_; size_t v_sz_795_; size_t v___x_796_; lean_object* v_decls_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_794_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_795_ = lean_array_size(v___y_793_);
v___x_796_ = ((size_t)0ULL);
v_decls_797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_794_, v___f_786_, v_sz_795_, v___x_796_, v___y_793_);
v___x_798_ = lean_array_to_list(v_decls_797_);
v___x_799_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_787_, v_inst_788_, v___x_798_, v_k_789_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_decls_817_, lean_object* v_k_818_){
_start:
{
lean_object* v_toBind_819_; lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___x_822_; 
v_toBind_819_ = lean_ctor_get(v_inst_814_, 1);
lean_inc(v_toBind_819_);
v___f_820_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_821_, 0, v___f_820_);
lean_closure_set(v___f_821_, 1, v_inst_815_);
lean_closure_set(v___f_821_, 2, v_inst_814_);
lean_closure_set(v___f_821_, 3, v_k_818_);
lean_closure_set(v___f_821_, 4, v_decls_817_);
v___x_822_ = lean_apply_4(v_toBind_819_, lean_box(0), lean_box(0), v_inst_816_, v___f_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_823_, lean_object* v_00_u03b1_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_decls_828_, lean_object* v_k_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_825_, v_inst_826_, v_inst_827_, v_decls_828_, v_k_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_831_, size_t v_i_832_, size_t v_stop_833_, lean_object* v_b_834_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_eq(v_i_832_, v_stop_833_);
if (v___x_835_ == 0)
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; lean_object* v_decl_839_; uint8_t v_isLet_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_sub(v_i_832_, v___x_836_);
v___x_838_ = lean_array_uget_borrowed(v_as_831_, v___x_837_);
v_decl_839_ = lean_ctor_get(v___x_838_, 0);
v_isLet_840_ = lean_ctor_get_uint8(v___x_838_, sizeof(void*)*1);
v___x_841_ = l_Lean_LocalDecl_userName(v_decl_839_);
v___x_842_ = l_Lean_LocalDecl_type(v_decl_839_);
v___x_843_ = l_Lean_LocalDecl_value(v_decl_839_, v___x_835_);
lean_inc_ref(v_decl_839_);
v___x_844_ = l_Lean_LocalDecl_toExpr(v_decl_839_);
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_mk_empty_array_with_capacity(v___x_845_);
v___x_847_ = lean_array_push(v___x_846_, v___x_844_);
v___x_848_ = lean_expr_abstract(v_b_834_, v___x_847_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v_b_834_);
if (v_isLet_840_ == 0)
{
uint8_t v___x_849_; lean_object* v___x_850_; 
v___x_849_ = 1;
v___x_850_ = l_Lean_Expr_letE___override(v___x_841_, v___x_842_, v___x_843_, v___x_848_, v___x_849_);
v_i_832_ = v___x_837_;
v_b_834_ = v___x_850_;
goto _start;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Expr_letE___override(v___x_841_, v___x_842_, v___x_843_, v___x_848_, v___x_835_);
v_i_832_ = v___x_837_;
v_b_834_ = v___x_852_;
goto _start;
}
}
else
{
return v_b_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object* v_as_854_, lean_object* v_i_855_, lean_object* v_stop_856_, lean_object* v_b_857_){
_start:
{
size_t v_i_boxed_858_; size_t v_stop_boxed_859_; lean_object* v_res_860_; 
v_i_boxed_858_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_stop_boxed_859_ = lean_unbox_usize(v_stop_856_);
lean_dec(v_stop_856_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_854_, v_i_boxed_858_, v_stop_boxed_859_, v_b_857_);
lean_dec_ref(v_as_854_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object* v_decls_861_, lean_object* v_e_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_863_ = lean_array_get_size(v_decls_861_);
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_nat_dec_lt(v___x_864_, v___x_863_);
if (v___x_865_ == 0)
{
return v_e_862_;
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_usize_of_nat(v___x_863_);
v___x_867_ = ((size_t)0ULL);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_861_, v___x_866_, v___x_867_, v_e_862_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object* v_decls_869_, lean_object* v_e_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_869_, v_e_870_);
lean_dec_ref(v_decls_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object* v_fvarId_872_, size_t v_sz_873_, size_t v_i_874_, lean_object* v_bs_875_){
_start:
{
uint8_t v___x_876_; 
v___x_876_ = lean_usize_dec_lt(v_i_874_, v_sz_873_);
if (v___x_876_ == 0)
{
return v_bs_875_;
}
else
{
lean_object* v_v_877_; lean_object* v_decl_878_; lean_object* v___x_879_; lean_object* v_bs_x27_880_; lean_object* v___y_882_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_v_877_ = lean_array_uget(v_bs_875_, v_i_874_);
v_decl_878_ = lean_ctor_get(v_v_877_, 0);
v___x_879_ = lean_unsigned_to_nat(0u);
v_bs_x27_880_ = lean_array_uset(v_bs_875_, v_i_874_, v___x_879_);
v___x_887_ = l_Lean_LocalDecl_fvarId(v_decl_878_);
v___x_888_ = l_Lean_instBEqFVarId_beq(v___x_887_, v_fvarId_872_);
lean_dec(v___x_887_);
if (v___x_888_ == 0)
{
v___y_882_ = v_v_877_;
goto v___jp_881_;
}
else
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_inc_ref(v_decl_878_);
v_isSharedCheck_895_ = !lean_is_exclusive(v_v_877_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_v_877_, 0);
lean_dec(v_unused_896_);
v___x_890_ = v_v_877_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_dec(v_v_877_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_decl_878_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_888_);
v___y_882_ = v___x_893_;
goto v___jp_881_;
}
}
}
v___jp_881_:
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_add(v_i_874_, v___x_883_);
v___x_885_ = lean_array_uset(v_bs_x27_880_, v_i_874_, v___y_882_);
v_i_874_ = v___x_884_;
v_bs_875_ = v___x_885_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object* v_fvarId_897_, lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_bs_900_){
_start:
{
size_t v_sz_boxed_901_; size_t v_i_boxed_902_; lean_object* v_res_903_; 
v_sz_boxed_901_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_902_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_897_, v_sz_boxed_901_, v_i_boxed_902_, v_bs_900_);
lean_dec(v_fvarId_897_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object* v_fvarId_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; lean_object* v_givenNames_908_; lean_object* v_decls_909_; lean_object* v_valueMap_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_923_; 
v___x_907_ = lean_st_ref_take(v_a_905_);
v_givenNames_908_ = lean_ctor_get(v___x_907_, 0);
v_decls_909_ = lean_ctor_get(v___x_907_, 1);
v_valueMap_910_ = lean_ctor_get(v___x_907_, 2);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_923_ == 0)
{
v___x_912_ = v___x_907_;
v_isShared_913_ = v_isSharedCheck_923_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_valueMap_910_);
lean_inc(v_decls_909_);
lean_inc(v_givenNames_908_);
lean_dec(v___x_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_923_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; size_t v_sz_915_; size_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_914_ = lean_box(0);
v_sz_915_ = lean_array_size(v_decls_909_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_904_, v_sz_915_, v___x_916_, v_decls_909_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_917_);
v___x_919_ = v___x_912_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_givenNames_908_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_valueMap_910_);
v___x_919_ = v_reuseFailAlloc_922_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_st_ref_put(v_a_905_, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_914_);
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object* v_fvarId_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec(v_fvarId_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object* v_fvarId_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_928_, v_a_931_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object* v_fvarId_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_fvarId_938_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(size_t v_sz_948_, size_t v_i_949_, lean_object* v_bs_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_lt(v_i_949_, v_sz_948_);
if (v___x_951_ == 0)
{
return v_bs_950_;
}
else
{
lean_object* v_v_952_; lean_object* v_decl_953_; lean_object* v___x_954_; lean_object* v_bs_x27_955_; size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v_v_952_ = lean_array_uget_borrowed(v_bs_950_, v_i_949_);
v_decl_953_ = lean_ctor_get(v_v_952_, 0);
lean_inc_ref(v_decl_953_);
v___x_954_ = lean_unsigned_to_nat(0u);
v_bs_x27_955_ = lean_array_uset(v_bs_950_, v_i_949_, v___x_954_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_add(v_i_949_, v___x_956_);
v___x_958_ = lean_array_uset(v_bs_x27_955_, v_i_949_, v_decl_953_);
v_i_949_ = v___x_957_;
v_bs_950_ = v___x_958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1___boxed(lean_object* v_sz_960_, lean_object* v_i_961_, lean_object* v_bs_962_){
_start:
{
size_t v_sz_boxed_963_; size_t v_i_boxed_964_; lean_object* v_res_965_; 
v_sz_boxed_963_ = lean_unbox_usize(v_sz_960_);
lean_dec(v_sz_960_);
v_i_boxed_964_ = lean_unbox_usize(v_i_961_);
lean_dec(v_i_961_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_boxed_963_, v_i_boxed_964_, v_bs_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(lean_object* v_x_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
lean_inc(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
v___x_975_ = lean_apply_8(v_x_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, lean_box(0));
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(v_x_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(lean_object* v_decls_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___f_996_; lean_object* v___x_997_; 
lean_inc(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
v___f_996_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_996_, 0, v_x_987_);
lean_closure_set(v___f_996_, 1, v___y_988_);
lean_closure_set(v___f_996_, 2, v___y_989_);
lean_closure_set(v___f_996_, 3, v___y_990_);
v___x_997_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_986_, v___f_996_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_997_) == 0)
{
return v___x_997_;
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___boxed(lean_object* v_decls_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1006_, v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(lean_object* v___x_1017_, lean_object* v_as_1018_, size_t v_i_1019_, size_t v_stop_1020_, lean_object* v_b_1021_){
_start:
{
lean_object* v___y_1023_; uint8_t v___x_1027_; 
v___x_1027_ = lean_usize_dec_eq(v_i_1019_, v_stop_1020_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v_decl_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1028_ = lean_array_uget_borrowed(v_as_1018_, v_i_1019_);
v_decl_1029_ = lean_ctor_get(v___x_1028_, 0);
v___x_1030_ = l_Lean_LocalDecl_fvarId(v_decl_1029_);
v___x_1031_ = l_Lean_LocalContext_contains(v___x_1017_, v___x_1030_);
lean_dec(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
lean_inc(v___x_1028_);
v___x_1032_ = lean_array_push(v_b_1021_, v___x_1028_);
v___y_1023_ = v___x_1032_;
goto v___jp_1022_;
}
else
{
v___y_1023_ = v_b_1021_;
goto v___jp_1022_;
}
}
else
{
return v_b_1021_;
}
v___jp_1022_:
{
size_t v___x_1024_; size_t v___x_1025_; 
v___x_1024_ = ((size_t)1ULL);
v___x_1025_ = lean_usize_add(v_i_1019_, v___x_1024_);
v_i_1019_ = v___x_1025_;
v_b_1021_ = v___y_1023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(lean_object* v___x_1033_, lean_object* v_as_1034_, lean_object* v_i_1035_, lean_object* v_stop_1036_, lean_object* v_b_1037_){
_start:
{
size_t v_i_boxed_1038_; size_t v_stop_boxed_1039_; lean_object* v_res_1040_; 
v_i_boxed_1038_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_stop_boxed_1039_ = lean_unbox_usize(v_stop_1036_);
lean_dec(v_stop_1036_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_1033_, v_as_1034_, v_i_boxed_1038_, v_stop_boxed_1039_, v_b_1037_);
lean_dec_ref(v_as_1034_);
lean_dec_ref(v___x_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(lean_object* v_decls_1041_, lean_object* v_k_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___y_1052_; lean_object* v_lctx_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_lctx_1058_ = lean_ctor_get(v___y_1046_, 2);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_array_get_size(v_decls_1041_);
v___x_1061_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_1062_ = lean_nat_dec_lt(v___x_1059_, v___x_1060_);
if (v___x_1062_ == 0)
{
v___y_1052_ = v___x_1061_;
goto v___jp_1051_;
}
else
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = lean_usize_of_nat(v___x_1060_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1058_, v_decls_1041_, v___x_1063_, v___x_1064_, v___x_1061_);
v___y_1052_ = v___x_1065_;
goto v___jp_1051_;
}
v___jp_1051_:
{
size_t v_sz_1053_; size_t v___x_1054_; lean_object* v_decls_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_sz_1053_ = lean_array_size(v___y_1052_);
v___x_1054_ = ((size_t)0ULL);
v_decls_1055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_1053_, v___x_1054_, v___y_1052_);
v___x_1056_ = lean_array_to_list(v_decls_1055_);
v___x_1057_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v___x_1056_, v_k_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object* v_decls_1066_, lean_object* v_k_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1066_, v_k_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v_decls_1066_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_fvarId_1077_, lean_object* v_as_1078_, lean_object* v_j_1079_){
_start:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_array_get_size(v_as_1078_);
v___x_1081_ = lean_nat_dec_lt(v_j_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v_j_1079_);
v___x_1082_ = lean_box(0);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v_decl_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1083_ = lean_array_fget_borrowed(v_as_1078_, v_j_1079_);
v_decl_1084_ = lean_ctor_get(v___x_1083_, 0);
v___x_1085_ = l_Lean_LocalDecl_fvarId(v_decl_1084_);
v___x_1086_ = l_Lean_instBEqFVarId_beq(v___x_1085_, v_fvarId_1077_);
lean_dec(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = lean_nat_add(v_j_1079_, v___x_1087_);
lean_dec(v_j_1079_);
v_j_1079_ = v___x_1088_;
goto _start;
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_j_1079_);
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_fvarId_1091_, lean_object* v_as_1092_, lean_object* v_j_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1091_, v_as_1092_, v_j_1093_);
lean_dec_ref(v_as_1092_);
lean_dec(v_fvarId_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1095_, lean_object* v_k_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_lctx_1106_; uint8_t v___x_1107_; 
v___x_1105_ = lean_st_ref_get(v_a_1099_);
v_lctx_1106_ = lean_ctor_get(v_a_1100_, 2);
v___x_1107_ = l_Lean_LocalContext_contains(v_lctx_1106_, v_fvarId_1095_);
if (v___x_1107_ == 0)
{
lean_object* v_decls_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_decls_1108_ = lean_ctor_get(v___x_1105_, 1);
lean_inc_ref(v_decls_1108_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1095_, v_decls_1108_, v___x_1109_);
if (lean_obj_tag(v___x_1110_) == 1)
{
lean_object* v_val_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_val_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_val_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_nat_add(v_val_1111_, v___x_1112_);
lean_dec(v_val_1111_);
v___x_1114_ = l_Array_toSubarray___redArg(v_decls_1108_, v___x_1109_, v___x_1113_);
v___x_1115_ = l_Subarray_copy___redArg(v___x_1114_);
v___x_1116_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_1115_, v_k_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec_ref(v___x_1115_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; 
lean_dec(v___x_1110_);
lean_dec_ref(v_decls_1108_);
lean_inc(v_a_1103_);
lean_inc_ref(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc_ref(v_a_1100_);
lean_inc(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
v___x_1117_ = lean_apply_8(v_k_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, lean_box(0));
return v___x_1117_;
}
}
else
{
lean_object* v___x_1118_; 
lean_dec(v___x_1105_);
lean_inc(v_a_1103_);
lean_inc_ref(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc_ref(v_a_1100_);
lean_inc(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
v___x_1118_ = lean_apply_8(v_k_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, lean_box(0));
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1119_, lean_object* v_k_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1119_, v_k_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_fvarId_1119_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1130_, lean_object* v_fvarId_1131_, lean_object* v_k_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1131_, v_k_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_fvarId_1143_, lean_object* v_k_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1142_, v_fvarId_1143_, v_k_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_fvarId_1143_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object* v_00_u03b1_1154_, lean_object* v_decls_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1155_, v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_decls_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_1166_, v_decls_1167_, v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object* v_00_u03b1_1178_, lean_object* v_decls_1179_, lean_object* v_k_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1179_, v_k_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_decls_1191_, lean_object* v_k_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_1190_, v_decls_1191_, v_k_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_decls_1191_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_Expr_hasMVar(v_e_1202_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_e_1202_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; lean_object* v_mctx_1208_; lean_object* v___x_1209_; lean_object* v_fst_1210_; lean_object* v_snd_1211_; lean_object* v___x_1212_; lean_object* v_cache_1213_; lean_object* v_zetaDeltaFVarIds_1214_; lean_object* v_postponed_1215_; lean_object* v_diag_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1225_; 
v___x_1207_ = lean_st_ref_get(v___y_1203_);
v_mctx_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_mctx_1208_);
lean_dec(v___x_1207_);
v___x_1209_ = l_Lean_instantiateMVarsCore(v_mctx_1208_, v_e_1202_);
v_fst_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_fst_1210_);
v_snd_1211_ = lean_ctor_get(v___x_1209_, 1);
lean_inc(v_snd_1211_);
lean_dec_ref(v___x_1209_);
v___x_1212_ = lean_st_ref_take(v___y_1203_);
v_cache_1213_ = lean_ctor_get(v___x_1212_, 1);
v_zetaDeltaFVarIds_1214_ = lean_ctor_get(v___x_1212_, 2);
v_postponed_1215_ = lean_ctor_get(v___x_1212_, 3);
v_diag_1216_ = lean_ctor_get(v___x_1212_, 4);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1212_, 0);
lean_dec(v_unused_1226_);
v___x_1218_ = v___x_1212_;
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_diag_1216_);
lean_inc(v_postponed_1215_);
lean_inc(v_zetaDeltaFVarIds_1214_);
lean_inc(v_cache_1213_);
lean_dec(v___x_1212_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v_snd_1211_);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_snd_1211_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_cache_1213_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_zetaDeltaFVarIds_1214_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_postponed_1215_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_diag_1216_);
v___x_1221_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_st_ref_put(v___y_1203_, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_fst_1210_);
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1227_, v___y_1228_);
lean_dec(v___y_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1231_, v___y_1236_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1251_, size_t v_i_1252_, size_t v_stop_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_a_1264_; uint8_t v___x_1270_; 
v___x_1270_ = lean_usize_dec_eq(v_i_1252_, v_stop_1253_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_array_uget_borrowed(v_as_1251_, v_i_1252_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_box(0);
v_a_1264_ = v___x_1272_;
goto v___jp_1263_;
}
else
{
lean_object* v_val_1273_; uint8_t v___y_1275_; uint8_t v___x_1302_; 
v_val_1273_ = lean_ctor_get(v___x_1271_, 0);
v___x_1302_ = l_Lean_LocalDecl_isLet(v_val_1273_, v___x_1270_);
if (v___x_1302_ == 0)
{
v___y_1275_ = v___x_1302_;
goto v___jp_1274_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1273_);
if (v___x_1303_ == 0)
{
v___y_1275_ = v___x_1302_;
goto v___jp_1274_;
}
else
{
goto v___jp_1268_;
}
}
v___jp_1274_:
{
if (v___y_1275_ == 0)
{
goto v___jp_1268_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = l_Lean_LocalDecl_value(v_val_1273_, v___x_1270_);
v___x_1277_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1276_, v___y_1259_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v_givenNames_1280_; lean_object* v_decls_1281_; lean_object* v_valueMap_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1293_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = lean_st_ref_take(v___y_1257_);
v_givenNames_1280_ = lean_ctor_get(v___x_1279_, 0);
v_decls_1281_ = lean_ctor_get(v___x_1279_, 1);
v_valueMap_1282_ = lean_ctor_get(v___x_1279_, 2);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1284_ = v___x_1279_;
v_isShared_1285_ = v_isSharedCheck_1293_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_valueMap_1282_);
lean_inc(v_decls_1281_);
lean_inc(v_givenNames_1280_);
lean_dec(v___x_1279_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1293_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1286_ = lean_box(0);
v___x_1287_ = l_Lean_LocalDecl_fvarId(v_val_1273_);
v___x_1288_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1282_, v_a_1278_, v___x_1287_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 2, v___x_1288_);
v___x_1290_ = v___x_1284_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_givenNames_1280_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_decls_1281_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_st_ref_put(v___y_1257_, v___x_1290_);
v_a_1264_ = v___x_1286_;
goto v___jp_1263_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1277_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1277_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_b_1254_);
return v___x_1304_;
}
v___jp_1263_:
{
size_t v___x_1265_; size_t v___x_1266_; 
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_add(v_i_1252_, v___x_1265_);
v_i_1252_ = v___x_1266_;
v_b_1254_ = v_a_1264_;
goto _start;
}
v___jp_1268_:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_box(0);
v_a_1264_ = v___x_1269_;
goto v___jp_1263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1305_, lean_object* v_i_1306_, lean_object* v_stop_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
size_t v_i_boxed_1317_; size_t v_stop_boxed_1318_; lean_object* v_res_1319_; 
v_i_boxed_1317_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_stop_boxed_1318_ = lean_unbox_usize(v_stop_1307_);
lean_dec(v_stop_1307_);
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1305_, v_i_boxed_1317_, v_stop_boxed_1318_, v_b_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_as_1305_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1320_, size_t v_i_1321_, size_t v_stop_1322_, lean_object* v_b_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_a_1333_; uint8_t v___x_1339_; 
v___x_1339_ = lean_usize_dec_eq(v_i_1321_, v_stop_1322_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_array_uget_borrowed(v_as_1320_, v_i_1321_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_box(0);
v_a_1333_ = v___x_1341_;
goto v___jp_1332_;
}
else
{
lean_object* v_val_1342_; uint8_t v___y_1344_; uint8_t v___x_1371_; 
v_val_1342_ = lean_ctor_get(v___x_1340_, 0);
v___x_1371_ = l_Lean_LocalDecl_isLet(v_val_1342_, v___x_1339_);
if (v___x_1371_ == 0)
{
v___y_1344_ = v___x_1371_;
goto v___jp_1343_;
}
else
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1342_);
if (v___x_1372_ == 0)
{
v___y_1344_ = v___x_1371_;
goto v___jp_1343_;
}
else
{
goto v___jp_1337_;
}
}
v___jp_1343_:
{
if (v___y_1344_ == 0)
{
goto v___jp_1337_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = l_Lean_LocalDecl_value(v_val_1342_, v___x_1339_);
v___x_1346_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1345_, v___y_1328_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v_givenNames_1349_; lean_object* v_decls_1350_; lean_object* v_valueMap_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1362_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = lean_st_ref_take(v___y_1326_);
v_givenNames_1349_ = lean_ctor_get(v___x_1348_, 0);
v_decls_1350_ = lean_ctor_get(v___x_1348_, 1);
v_valueMap_1351_ = lean_ctor_get(v___x_1348_, 2);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1353_ = v___x_1348_;
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_valueMap_1351_);
lean_inc(v_decls_1350_);
lean_inc(v_givenNames_1349_);
lean_dec(v___x_1348_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = l_Lean_LocalDecl_fvarId(v_val_1342_);
v___x_1357_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1351_, v_a_1347_, v___x_1356_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 2, v___x_1357_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_givenNames_1349_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_decls_1350_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_st_ref_put(v___y_1326_, v___x_1359_);
v_a_1333_ = v___x_1355_;
goto v___jp_1332_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_a_1363_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1346_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1346_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_b_1323_);
return v___x_1373_;
}
v___jp_1332_:
{
size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1321_, v___x_1334_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1320_, v___x_1335_, v_stop_1322_, v_a_1333_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
return v___x_1336_;
}
v___jp_1337_:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_box(0);
v_a_1333_ = v___x_1338_;
goto v___jp_1332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1374_, lean_object* v_i_1375_, lean_object* v_stop_1376_, lean_object* v_b_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
size_t v_i_boxed_1386_; size_t v_stop_boxed_1387_; lean_object* v_res_1388_; 
v_i_boxed_1386_ = lean_unbox_usize(v_i_1375_);
lean_dec(v_i_1375_);
v_stop_boxed_1387_ = lean_unbox_usize(v_stop_1376_);
lean_dec(v_stop_1376_);
v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1374_, v_i_boxed_1386_, v_stop_boxed_1387_, v_b_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v_as_1374_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v_cs_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1412_; 
v_cs_1398_ = lean_ctor_get(v_x_1389_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1400_ = v_x_1389_;
v_isShared_1401_ = v_isSharedCheck_1412_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_cs_1398_);
lean_dec(v_x_1389_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1412_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_array_get_size(v_cs_1398_);
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_nat_dec_lt(v___x_1402_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1407_; 
lean_dec_ref(v_cs_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1404_);
v___x_1407_ = v___x_1400_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1404_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
lean_del_object(v___x_1400_);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1403_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1398_, v___x_1409_, v___x_1410_, v___x_1404_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec_ref(v_cs_1398_);
return v___x_1411_;
}
}
}
else
{
lean_object* v_vs_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1427_; 
v_vs_1413_ = lean_ctor_get(v_x_1389_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1415_ = v_x_1389_;
v_isShared_1416_ = v_isSharedCheck_1427_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_vs_1413_);
lean_dec(v_x_1389_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1427_;
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
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
lean_del_object(v___x_1415_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1418_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1413_, v___x_1424_, v___x_1425_, v___x_1419_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec_ref(v_vs_1413_);
return v___x_1426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1428_, size_t v_i_1429_, size_t v_stop_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_usize_dec_eq(v_i_1429_, v_stop_1430_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_array_uget_borrowed(v_as_1428_, v_i_1429_);
lean_inc(v___x_1441_);
v___x_1442_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1441_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; size_t v___x_1444_; size_t v___x_1445_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = ((size_t)1ULL);
v___x_1445_ = lean_usize_add(v_i_1429_, v___x_1444_);
v_i_1429_ = v___x_1445_;
v_b_1431_ = v_a_1443_;
goto _start;
}
else
{
return v___x_1442_;
}
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1431_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1448_, lean_object* v_i_1449_, lean_object* v_stop_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
size_t v_i_boxed_1460_; size_t v_stop_boxed_1461_; lean_object* v_res_1462_; 
v_i_boxed_1460_ = lean_unbox_usize(v_i_1449_);
lean_dec(v_i_1449_);
v_stop_boxed_1461_ = lean_unbox_usize(v_stop_1450_);
lean_dec(v_stop_1450_);
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1448_, v_i_boxed_1460_, v_stop_boxed_1461_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v_as_1448_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_root_1482_; lean_object* v_tail_1483_; lean_object* v___x_1484_; 
v_root_1482_ = lean_ctor_get(v_t_1473_, 0);
lean_inc_ref(v_root_1482_);
v_tail_1483_ = lean_ctor_get(v_t_1473_, 1);
lean_inc_ref(v_tail_1483_);
lean_dec_ref(v_t_1473_);
v___x_1484_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1482_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1498_; 
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v___x_1484_, 0);
lean_dec(v_unused_1499_);
v___x_1486_ = v___x_1484_;
v_isShared_1487_ = v_isSharedCheck_1498_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v___x_1484_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1498_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_array_get_size(v_tail_1483_);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_nat_dec_lt(v___x_1488_, v___x_1489_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1493_; 
lean_dec_ref(v_tail_1483_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1490_);
v___x_1493_ = v___x_1486_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1490_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
else
{
size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
lean_del_object(v___x_1486_);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = lean_usize_of_nat(v___x_1489_);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1483_, v___x_1495_, v___x_1496_, v___x_1490_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec_ref(v_tail_1483_);
return v___x_1497_;
}
}
}
else
{
lean_dec_ref(v_tail_1483_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1509_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1511_, size_t v_x_1512_, size_t v_x_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 0)
{
lean_object* v_cs_1522_; lean_object* v___x_1523_; size_t v___x_1524_; lean_object* v_j_1525_; lean_object* v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v_cs_1522_ = lean_ctor_get(v_x_1511_, 0);
lean_inc_ref(v_cs_1522_);
lean_dec_ref_known(v_x_1511_, 1);
v___x_1523_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1524_ = lean_usize_shift_right(v_x_1512_, v_x_1513_);
v_j_1525_ = lean_usize_to_nat(v___x_1524_);
v___x_1526_ = lean_array_get_borrowed(v___x_1523_, v_cs_1522_, v_j_1525_);
v___x_1527_ = ((size_t)1ULL);
v___x_1528_ = lean_usize_shift_left(v___x_1527_, v_x_1513_);
v___x_1529_ = lean_usize_sub(v___x_1528_, v___x_1527_);
v___x_1530_ = lean_usize_land(v_x_1512_, v___x_1529_);
v___x_1531_ = ((size_t)5ULL);
v___x_1532_ = lean_usize_sub(v_x_1513_, v___x_1531_);
lean_inc(v___x_1526_);
v___x_1533_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1526_, v___x_1530_, v___x_1532_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1548_; 
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v___x_1533_, 0);
lean_dec(v_unused_1549_);
v___x_1535_ = v___x_1533_;
v_isShared_1536_ = v_isSharedCheck_1548_;
goto v_resetjp_1534_;
}
else
{
lean_dec(v___x_1533_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1548_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_add(v_j_1525_, v___x_1537_);
lean_dec(v_j_1525_);
v___x_1539_ = lean_array_get_size(v_cs_1522_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_nat_dec_lt(v___x_1538_, v___x_1539_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1543_; 
lean_dec(v___x_1538_);
lean_dec_ref(v_cs_1522_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1540_);
v___x_1543_ = v___x_1535_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1540_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
lean_del_object(v___x_1535_);
v___x_1545_ = lean_usize_of_nat(v___x_1538_);
lean_dec(v___x_1538_);
v___x_1546_ = lean_usize_of_nat(v___x_1539_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1522_, v___x_1545_, v___x_1546_, v___x_1540_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec_ref(v_cs_1522_);
return v___x_1547_;
}
}
}
else
{
lean_dec(v_j_1525_);
lean_dec_ref(v_cs_1522_);
return v___x_1533_;
}
}
else
{
lean_object* v_vs_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1564_; 
v_vs_1550_ = lean_ctor_get(v_x_1511_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1552_ = v_x_1511_;
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_vs_1550_);
lean_dec(v_x_1511_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1554_ = lean_usize_to_nat(v_x_1512_);
v___x_1555_ = lean_array_get_size(v_vs_1550_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_nat_dec_lt(v___x_1554_, v___x_1555_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1559_; 
lean_dec(v___x_1554_);
lean_dec_ref(v_vs_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1556_);
v___x_1559_ = v___x_1552_;
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
size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
lean_del_object(v___x_1552_);
v___x_1561_ = lean_usize_of_nat(v___x_1554_);
lean_dec(v___x_1554_);
v___x_1562_ = lean_usize_of_nat(v___x_1555_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1550_, v___x_1561_, v___x_1562_, v___x_1556_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec_ref(v_vs_1550_);
return v___x_1563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
size_t v_x_9185__boxed_1576_; size_t v_x_9186__boxed_1577_; lean_object* v_res_1578_; 
v_x_9185__boxed_1576_ = lean_unbox_usize(v_x_1566_);
lean_dec(v_x_1566_);
v_x_9186__boxed_1577_ = lean_unbox_usize(v_x_1567_);
lean_dec(v_x_1567_);
v_res_1578_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1565_, v_x_9185__boxed_1576_, v_x_9186__boxed_1577_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1579_, lean_object* v_start_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = lean_nat_dec_eq(v_start_1580_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_object* v_root_1591_; lean_object* v_tail_1592_; size_t v_shift_1593_; lean_object* v_tailOff_1594_; uint8_t v___x_1595_; 
v_root_1591_ = lean_ctor_get(v_t_1579_, 0);
lean_inc_ref(v_root_1591_);
v_tail_1592_ = lean_ctor_get(v_t_1579_, 1);
lean_inc_ref(v_tail_1592_);
v_shift_1593_ = lean_ctor_get_usize(v_t_1579_, 4);
v_tailOff_1594_ = lean_ctor_get(v_t_1579_, 3);
lean_inc(v_tailOff_1594_);
lean_dec_ref(v_t_1579_);
v___x_1595_ = lean_nat_dec_le(v_tailOff_1594_, v_start_1580_);
if (v___x_1595_ == 0)
{
size_t v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_tailOff_1594_);
v___x_1596_ = lean_usize_of_nat(v_start_1580_);
v___x_1597_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1591_, v___x_1596_, v_shift_1593_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1610_; 
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v___x_1597_, 0);
lean_dec(v_unused_1611_);
v___x_1599_ = v___x_1597_;
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v___x_1597_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1601_ = lean_array_get_size(v_tail_1592_);
v___x_1602_ = lean_box(0);
v___x_1603_ = lean_nat_dec_lt(v___x_1589_, v___x_1601_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref(v_tail_1592_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1602_);
v___x_1605_ = v___x_1599_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1602_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
size_t v___x_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
lean_del_object(v___x_1599_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = lean_usize_of_nat(v___x_1601_);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1592_, v___x_1607_, v___x_1608_, v___x_1602_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec_ref(v_tail_1592_);
return v___x_1609_;
}
}
}
else
{
lean_dec_ref(v_tail_1592_);
return v___x_1597_;
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
lean_dec_ref(v_root_1591_);
v___x_1612_ = lean_nat_sub(v_start_1580_, v_tailOff_1594_);
lean_dec(v_tailOff_1594_);
v___x_1613_ = lean_array_get_size(v_tail_1592_);
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_nat_dec_lt(v___x_1612_, v___x_1613_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
lean_dec(v___x_1612_);
lean_dec_ref(v_tail_1592_);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
return v___x_1616_;
}
else
{
size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_usize_of_nat(v___x_1612_);
lean_dec(v___x_1612_);
v___x_1618_ = lean_usize_of_nat(v___x_1613_);
v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1592_, v___x_1617_, v___x_1618_, v___x_1614_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec_ref(v_tail_1592_);
return v___x_1619_;
}
}
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1579_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1621_, lean_object* v_start_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1621_, v_start_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v_start_1622_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1632_, lean_object* v_start_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_decls_1642_; lean_object* v___x_1643_; 
v_decls_1642_ = lean_ctor_get(v_lctx_1632_, 1);
lean_inc_ref(v_decls_1642_);
lean_dec_ref(v_lctx_1632_);
v___x_1643_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1642_, v_start_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1644_, lean_object* v_start_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1644_, v_start_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v_start_1645_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_lctx_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_lctx_1663_ = lean_ctor_get(v_a_1658_, 2);
v___x_1664_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1663_);
v___x_1665_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1663_, v___x_1664_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1676_){
_start:
{
lean_object* v___f_1677_; lean_object* v___x_1678_; 
v___f_1677_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1678_ = lean_find_expr(v___f_1677_, v_e_1676_);
if (lean_obj_tag(v___x_1678_) == 0)
{
uint8_t v___x_1679_; 
v___x_1679_ = 0;
return v___x_1679_;
}
else
{
uint8_t v___x_1680_; 
lean_dec_ref_known(v___x_1678_, 1);
v___x_1680_ = 1;
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1681_){
_start:
{
uint8_t v_res_1682_; lean_object* v_r_1683_; 
v_res_1682_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1681_);
lean_dec_ref(v_e_1681_);
v_r_1683_ = lean_box(v_res_1682_);
return v_r_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
v___x_1694_ = lean_apply_9(v_k_1684_, v_b_1688_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, lean_box(0));
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v_b_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v_b_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1706_, uint8_t v_bi_1707_, lean_object* v_type_1708_, lean_object* v_k_1709_, uint8_t v_kind_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___f_1719_; lean_object* v___x_1720_; 
lean_inc(v___y_1713_);
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1719_, 0, v_k_1709_);
lean_closure_set(v___f_1719_, 1, v___y_1711_);
lean_closure_set(v___f_1719_, 2, v___y_1712_);
lean_closure_set(v___f_1719_, 3, v___y_1713_);
v___x_1720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1706_, v_bi_1707_, v_type_1708_, v___f_1719_, v_kind_1710_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1720_) == 0)
{
return v___x_1720_;
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1729_, lean_object* v_bi_1730_, lean_object* v_type_1731_, lean_object* v_k_1732_, lean_object* v_kind_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_bi_boxed_1742_; uint8_t v_kind_boxed_1743_; lean_object* v_res_1744_; 
v_bi_boxed_1742_ = lean_unbox(v_bi_1730_);
v_kind_boxed_1743_ = lean_unbox(v_kind_1733_);
v_res_1744_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1729_, v_bi_boxed_1742_, v_type_1731_, v_k_1732_, v_kind_boxed_1743_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1745_, lean_object* v_name_1746_, uint8_t v_bi_1747_, lean_object* v_type_1748_, lean_object* v_k_1749_, uint8_t v_kind_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1746_, v_bi_1747_, v_type_1748_, v_k_1749_, v_kind_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1760_, lean_object* v_name_1761_, lean_object* v_bi_1762_, lean_object* v_type_1763_, lean_object* v_k_1764_, lean_object* v_kind_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
uint8_t v_bi_boxed_1774_; uint8_t v_kind_boxed_1775_; lean_object* v_res_1776_; 
v_bi_boxed_1774_ = lean_unbox(v_bi_1762_);
v_kind_boxed_1775_ = lean_unbox(v_kind_1765_);
v_res_1776_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1760_, v_name_1761_, v_bi_boxed_1774_, v_type_1763_, v_k_1764_, v_kind_boxed_1775_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1777_, lean_object* v_e_1778_, lean_object* v___f_1779_, lean_object* v_____r_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
if (v_types_1777_ == 0)
{
lean_object* v___x_1789_; 
lean_inc_ref(v_e_1778_);
v___x_1789_ = l_Lean_Meta_isType(v_e_1778_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1800_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_unbox(v_a_1790_);
lean_dec(v_a_1790_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_del_object(v___x_1792_);
lean_dec_ref(v_e_1778_);
v___x_1795_ = lean_box(0);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
v___x_1796_ = lean_apply_9(v___f_1779_, v___x_1795_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, lean_box(0));
return v___x_1796_;
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref(v___f_1779_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_e_1778_);
v___x_1798_ = v___x_1792_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_e_1778_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v___f_1779_);
lean_dec_ref(v_e_1778_);
v_a_1801_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1789_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1789_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec_ref(v_e_1778_);
v___x_1809_ = lean_box(0);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
v___x_1810_ = lean_apply_9(v___f_1779_, v___x_1809_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, lean_box(0));
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1811_, lean_object* v_e_1812_, lean_object* v___f_1813_, lean_object* v_____r_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v_types_boxed_1823_; lean_object* v_res_1824_; 
v_types_boxed_1823_ = lean_unbox(v_types_1811_);
v_res_1824_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1823_, v_e_1812_, v___f_1813_, v_____r_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v_res_1824_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1825_, uint8_t v___y_1826_){
_start:
{
if (v___y_1826_ == 0)
{
if (v___y_1825_ == 0)
{
uint8_t v___x_1827_; 
v___x_1827_ = 1;
return v___x_1827_;
}
else
{
return v___y_1826_;
}
}
else
{
return v___y_1825_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v___y_41155__boxed_1830_; uint8_t v___y_41156__boxed_1831_; uint8_t v_res_1832_; lean_object* v_r_1833_; 
v___y_41155__boxed_1830_ = lean_unbox(v___y_1828_);
v___y_41156__boxed_1831_ = lean_unbox(v___y_1829_);
v_res_1832_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_41155__boxed_1830_, v___y_41156__boxed_1831_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_instMonadEIO___redArg();
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_toApplicative_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1925_; 
v___x_1851_ = lean_box(0);
v___x_1852_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1853_ = l_StateRefT_x27_instMonad___redArg(v___x_1852_);
v_toApplicative_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v___x_1853_, 1);
lean_dec(v_unused_1926_);
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1925_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_toApplicative_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1925_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_toFunctor_1858_; lean_object* v_toSeq_1859_; lean_object* v_toSeqLeft_1860_; lean_object* v_toSeqRight_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1923_; 
v_toFunctor_1858_ = lean_ctor_get(v_toApplicative_1854_, 0);
v_toSeq_1859_ = lean_ctor_get(v_toApplicative_1854_, 2);
v_toSeqLeft_1860_ = lean_ctor_get(v_toApplicative_1854_, 3);
v_toSeqRight_1861_ = lean_ctor_get(v_toApplicative_1854_, 4);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_toApplicative_1854_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v_toApplicative_1854_, 1);
lean_dec(v_unused_1924_);
v___x_1863_ = v_toApplicative_1854_;
v_isShared_1864_ = v_isSharedCheck_1923_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_toSeqRight_1861_);
lean_inc(v_toSeqLeft_1860_);
lean_inc(v_toSeq_1859_);
lean_inc(v_toFunctor_1858_);
lean_dec(v_toApplicative_1854_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1923_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___f_1865_; lean_object* v___f_1866_; lean_object* v___f_1867_; lean_object* v___f_1868_; lean_object* v___x_1869_; lean_object* v___f_1870_; lean_object* v___f_1871_; lean_object* v___f_1872_; lean_object* v___x_1874_; 
v___f_1865_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1866_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1858_);
v___f_1867_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1867_, 0, v_toFunctor_1858_);
v___f_1868_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1868_, 0, v_toFunctor_1858_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___f_1867_);
lean_ctor_set(v___x_1869_, 1, v___f_1868_);
v___f_1870_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1870_, 0, v_toSeqRight_1861_);
v___f_1871_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1871_, 0, v_toSeqLeft_1860_);
v___f_1872_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1872_, 0, v_toSeq_1859_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 4, v___f_1870_);
lean_ctor_set(v___x_1863_, 3, v___f_1871_);
lean_ctor_set(v___x_1863_, 2, v___f_1872_);
lean_ctor_set(v___x_1863_, 1, v___f_1865_);
lean_ctor_set(v___x_1863_, 0, v___x_1869_);
v___x_1874_ = v___x_1863_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___f_1865_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v___f_1872_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v___f_1871_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v___f_1870_);
v___x_1874_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 1, v___f_1866_);
lean_ctor_set(v___x_1856_, 0, v___x_1874_);
v___x_1876_ = v___x_1856_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___f_1866_);
v___x_1876_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v_toApplicative_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1919_; 
v___x_1877_ = l_StateRefT_x27_instMonad___redArg(v___x_1876_);
v_toApplicative_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v___x_1877_, 1);
lean_dec(v_unused_1920_);
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1919_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_toApplicative_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1919_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_toFunctor_1882_; lean_object* v_toSeq_1883_; lean_object* v_toSeqLeft_1884_; lean_object* v_toSeqRight_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1917_; 
v_toFunctor_1882_ = lean_ctor_get(v_toApplicative_1878_, 0);
v_toSeq_1883_ = lean_ctor_get(v_toApplicative_1878_, 2);
v_toSeqLeft_1884_ = lean_ctor_get(v_toApplicative_1878_, 3);
v_toSeqRight_1885_ = lean_ctor_get(v_toApplicative_1878_, 4);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_toApplicative_1878_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_toApplicative_1878_, 1);
lean_dec(v_unused_1918_);
v___x_1887_ = v_toApplicative_1878_;
v_isShared_1888_ = v_isSharedCheck_1917_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_toSeqRight_1885_);
lean_inc(v_toSeqLeft_1884_);
lean_inc(v_toSeq_1883_);
lean_inc(v_toFunctor_1882_);
lean_dec(v_toApplicative_1878_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1917_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___f_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___f_1895_; lean_object* v___f_1896_; lean_object* v___f_1897_; lean_object* v___f_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___f_1901_; lean_object* v___f_1902_; lean_object* v___f_1903_; lean_object* v___x_1905_; 
v___f_1889_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1890_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1890_, 0, v___f_1889_);
v___x_1891_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1892_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1892_, 0, v___f_1890_);
lean_closure_set(v___f_1892_, 1, v___x_1891_);
v___f_1893_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1894_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1895_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1895_, 0, v___f_1893_);
lean_closure_set(v___f_1895_, 1, v___x_1894_);
v___f_1896_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1897_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1882_);
v___f_1898_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1898_, 0, v_toFunctor_1882_);
v___f_1899_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1899_, 0, v_toFunctor_1882_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___f_1898_);
lean_ctor_set(v___x_1900_, 1, v___f_1899_);
v___f_1901_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1901_, 0, v_toSeqRight_1885_);
v___f_1902_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1902_, 0, v_toSeqLeft_1884_);
v___f_1903_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1903_, 0, v_toSeq_1883_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 4, v___f_1901_);
lean_ctor_set(v___x_1887_, 3, v___f_1902_);
lean_ctor_set(v___x_1887_, 2, v___f_1903_);
lean_ctor_set(v___x_1887_, 1, v___f_1896_);
lean_ctor_set(v___x_1887_, 0, v___x_1900_);
v___x_1905_ = v___x_1887_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___f_1896_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v___f_1903_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v___f_1902_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v___f_1901_);
v___x_1905_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1907_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 1, v___f_1897_);
lean_ctor_set(v___x_1880_, 0, v___x_1905_);
v___x_1907_ = v___x_1880_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___f_1897_);
v___x_1907_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_37996__overap_1913_; lean_object* v___x_1914_; 
v___x_1908_ = l_StateRefT_x27_instMonad___redArg(v___x_1907_);
v___x_1909_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1851_, v___f_1892_, v___f_1895_, v___x_1908_);
v___x_1910_ = l_Lean_instInhabitedExpr;
v___x_1911_ = l_instInhabitedOfMonad___redArg(v___x_1909_, v___x_1910_);
v___f_1912_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1912_, 0, v___x_1911_);
v___x_37996__overap_1913_ = lean_panic_fn_borrowed(v___f_1912_, v_msg_1842_);
lean_dec_ref(v___f_1912_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v___y_1847_);
lean_inc_ref(v___y_1846_);
lean_inc(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
v___x_1914_ = lean_apply_8(v___x_37996__overap_1913_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, lean_box(0));
return v___x_1914_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderType_1937_, lean_object* v_binderName_1938_, uint8_t v_binderInfo_1939_, lean_object* v_body_1940_, lean_object* v_e_1941_, lean_object* v_t_1942_, lean_object* v_b_1943_){
_start:
{
size_t v___x_1944_; size_t v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = lean_ptr_addr(v_binderType_1937_);
v___x_1945_ = lean_ptr_addr(v_t_1942_);
v___x_1946_ = lean_usize_dec_eq(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Expr_lam___override(v_binderName_1938_, v_t_1942_, v_b_1943_, v_binderInfo_1939_);
return v___x_1947_;
}
else
{
size_t v___x_1948_; size_t v___x_1949_; uint8_t v___x_1950_; 
v___x_1948_ = lean_ptr_addr(v_body_1940_);
v___x_1949_ = lean_ptr_addr(v_b_1943_);
v___x_1950_ = lean_usize_dec_eq(v___x_1948_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Expr_lam___override(v_binderName_1938_, v_t_1942_, v_b_1943_, v_binderInfo_1939_);
return v___x_1951_;
}
else
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1939_, v_binderInfo_1939_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_Expr_lam___override(v_binderName_1938_, v_t_1942_, v_b_1943_, v_binderInfo_1939_);
return v___x_1953_;
}
else
{
lean_dec_ref(v_b_1943_);
lean_dec_ref(v_t_1942_);
lean_dec(v_binderName_1938_);
lean_inc_ref(v_e_1941_);
return v_e_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderType_1954_, lean_object* v_binderName_1955_, lean_object* v_binderInfo_1956_, lean_object* v_body_1957_, lean_object* v_e_1958_, lean_object* v_t_1959_, lean_object* v_b_1960_){
_start:
{
uint8_t v_binderInfo_41343__boxed_1961_; lean_object* v_res_1962_; 
v_binderInfo_41343__boxed_1961_ = lean_unbox(v_binderInfo_1956_);
v_res_1962_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderType_1954_, v_binderName_1955_, v_binderInfo_41343__boxed_1961_, v_body_1957_, v_e_1958_, v_t_1959_, v_b_1960_);
lean_dec_ref(v_e_1958_);
lean_dec_ref(v_body_1957_);
lean_dec_ref(v_binderType_1954_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderType_1963_, lean_object* v_binderName_1964_, uint8_t v_binderInfo_1965_, lean_object* v_body_1966_, lean_object* v_e_1967_, lean_object* v_t_1968_, lean_object* v_b_1969_){
_start:
{
size_t v___x_1970_; size_t v___x_1971_; uint8_t v___x_1972_; 
v___x_1970_ = lean_ptr_addr(v_binderType_1963_);
v___x_1971_ = lean_ptr_addr(v_t_1968_);
v___x_1972_ = lean_usize_dec_eq(v___x_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Expr_forallE___override(v_binderName_1964_, v_t_1968_, v_b_1969_, v_binderInfo_1965_);
return v___x_1973_;
}
else
{
size_t v___x_1974_; size_t v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = lean_ptr_addr(v_body_1966_);
v___x_1975_ = lean_ptr_addr(v_b_1969_);
v___x_1976_ = lean_usize_dec_eq(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Expr_forallE___override(v_binderName_1964_, v_t_1968_, v_b_1969_, v_binderInfo_1965_);
return v___x_1977_;
}
else
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1965_, v_binderInfo_1965_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Expr_forallE___override(v_binderName_1964_, v_t_1968_, v_b_1969_, v_binderInfo_1965_);
return v___x_1979_;
}
else
{
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_t_1968_);
lean_dec(v_binderName_1964_);
lean_inc_ref(v_e_1967_);
return v_e_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderType_1980_, lean_object* v_binderName_1981_, lean_object* v_binderInfo_1982_, lean_object* v_body_1983_, lean_object* v_e_1984_, lean_object* v_t_1985_, lean_object* v_b_1986_){
_start:
{
uint8_t v_binderInfo_41375__boxed_1987_; lean_object* v_res_1988_; 
v_binderInfo_41375__boxed_1987_ = lean_unbox(v_binderInfo_1982_);
v_res_1988_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderType_1980_, v_binderName_1981_, v_binderInfo_41375__boxed_1987_, v_body_1983_, v_e_1984_, v_t_1985_, v_b_1986_);
lean_dec_ref(v_e_1984_);
lean_dec_ref(v_body_1983_);
lean_dec_ref(v_binderType_1980_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_1989_, lean_object* v_type_1990_, lean_object* v_val_1991_, lean_object* v_k_1992_, uint8_t v_nondep_1993_, uint8_t v_kind_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___f_2003_; lean_object* v___x_2004_; 
lean_inc(v___y_1997_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
v___f_2003_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2003_, 0, v_k_1992_);
lean_closure_set(v___f_2003_, 1, v___y_1995_);
lean_closure_set(v___f_2003_, 2, v___y_1996_);
lean_closure_set(v___f_2003_, 3, v___y_1997_);
v___x_2004_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1989_, v_type_1990_, v_val_1991_, v___f_2003_, v_nondep_1993_, v_kind_1994_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2004_) == 0)
{
return v___x_2004_;
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2013_, lean_object* v_type_2014_, lean_object* v_val_2015_, lean_object* v_k_2016_, lean_object* v_nondep_2017_, lean_object* v_kind_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_nondep_boxed_2027_; uint8_t v_kind_boxed_2028_; lean_object* v_res_2029_; 
v_nondep_boxed_2027_ = lean_unbox(v_nondep_2017_);
v_kind_boxed_2028_ = lean_unbox(v_kind_2018_);
v_res_2029_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2013_, v_type_2014_, v_val_2015_, v_k_2016_, v_nondep_boxed_2027_, v_kind_boxed_2028_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2030_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = l_Lean_instInhabitedExpr;
v___x_2032_ = lean_panic_fn_borrowed(v___x_2031_, v_msg_2030_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2033_, lean_object* v_x_2034_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_box(0);
return v___x_2035_;
}
else
{
lean_object* v_key_2036_; lean_object* v_value_2037_; lean_object* v_tail_2038_; uint8_t v___x_2039_; 
v_key_2036_ = lean_ctor_get(v_x_2034_, 0);
v_value_2037_ = lean_ctor_get(v_x_2034_, 1);
v_tail_2038_ = lean_ctor_get(v_x_2034_, 2);
v___x_2039_ = l_Lean_ExprStructEq_beq(v_key_2036_, v_a_2033_);
if (v___x_2039_ == 0)
{
v_x_2034_ = v_tail_2038_;
goto _start;
}
else
{
lean_object* v___x_2041_; 
lean_inc(v_value_2037_);
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_value_2037_);
return v___x_2041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2042_, v_x_2043_);
lean_dec(v_x_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_buckets_2047_; lean_object* v___x_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; uint64_t v___x_2051_; uint64_t v_fold_2052_; uint64_t v___x_2053_; uint64_t v___x_2054_; uint64_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; size_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_buckets_2047_ = lean_ctor_get(v_m_2045_, 1);
v___x_2048_ = lean_array_get_size(v_buckets_2047_);
v___x_2049_ = l_Lean_ExprStructEq_hash(v_a_2046_);
v___x_2050_ = 32ULL;
v___x_2051_ = lean_uint64_shift_right(v___x_2049_, v___x_2050_);
v_fold_2052_ = lean_uint64_xor(v___x_2049_, v___x_2051_);
v___x_2053_ = 16ULL;
v___x_2054_ = lean_uint64_shift_right(v_fold_2052_, v___x_2053_);
v___x_2055_ = lean_uint64_xor(v_fold_2052_, v___x_2054_);
v___x_2056_ = lean_uint64_to_usize(v___x_2055_);
v___x_2057_ = lean_usize_of_nat(v___x_2048_);
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_sub(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_usize_land(v___x_2056_, v___x_2059_);
v___x_2061_ = lean_array_uget_borrowed(v_buckets_2047_, v___x_2060_);
v___x_2062_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2046_, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2063_, v_a_2064_);
lean_dec_ref(v_a_2064_);
lean_dec_ref(v_m_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2066_, lean_object* v_x_2067_){
_start:
{
if (lean_obj_tag(v_x_2067_) == 0)
{
uint8_t v___x_2068_; 
v___x_2068_ = 0;
return v___x_2068_;
}
else
{
lean_object* v_key_2069_; lean_object* v_tail_2070_; lean_object* v_fst_2071_; lean_object* v_snd_2072_; lean_object* v_fst_2073_; lean_object* v_snd_2074_; uint8_t v___x_2078_; 
v_key_2069_ = lean_ctor_get(v_x_2067_, 0);
v_tail_2070_ = lean_ctor_get(v_x_2067_, 2);
v_fst_2071_ = lean_ctor_get(v_key_2069_, 0);
v_snd_2072_ = lean_ctor_get(v_key_2069_, 1);
v_fst_2073_ = lean_ctor_get(v_a_2066_, 0);
v_snd_2074_ = lean_ctor_get(v_a_2066_, 1);
v___x_2078_ = lean_unbox(v_fst_2073_);
if (v___x_2078_ == 0)
{
uint8_t v___x_2079_; 
v___x_2079_ = lean_unbox(v_fst_2071_);
if (v___x_2079_ == 0)
{
goto v___jp_2075_;
}
else
{
v_x_2067_ = v_tail_2070_;
goto _start;
}
}
else
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_unbox(v_fst_2071_);
if (v___x_2081_ == 0)
{
v_x_2067_ = v_tail_2070_;
goto _start;
}
else
{
goto v___jp_2075_;
}
}
v___jp_2075_:
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Lean_ExprStructEq_beq(v_snd_2072_, v_snd_2074_);
if (v___x_2076_ == 0)
{
v_x_2067_ = v_tail_2070_;
goto _start;
}
else
{
return v___x_2076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2083_, lean_object* v_x_2084_){
_start:
{
uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_res_2085_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2083_, v_x_2084_);
lean_dec(v_x_2084_);
lean_dec_ref(v_a_2083_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2087_, lean_object* v_b_2088_, lean_object* v_x_2089_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 0)
{
lean_dec(v_b_2088_);
lean_dec_ref(v_a_2087_);
return v_x_2089_;
}
else
{
lean_object* v_key_2090_; lean_object* v_value_2091_; lean_object* v_tail_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2111_; 
v_key_2090_ = lean_ctor_get(v_x_2089_, 0);
v_value_2091_ = lean_ctor_get(v_x_2089_, 1);
v_tail_2092_ = lean_ctor_get(v_x_2089_, 2);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_2089_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2094_ = v_x_2089_;
v_isShared_2095_ = v_isSharedCheck_2111_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_tail_2092_);
lean_inc(v_value_2091_);
lean_inc(v_key_2090_);
lean_dec(v_x_2089_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2111_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_fst_2101_; lean_object* v_snd_2102_; lean_object* v_fst_2103_; lean_object* v_snd_2104_; uint8_t v___x_2108_; 
v_fst_2101_ = lean_ctor_get(v_key_2090_, 0);
v_snd_2102_ = lean_ctor_get(v_key_2090_, 1);
v_fst_2103_ = lean_ctor_get(v_a_2087_, 0);
v_snd_2104_ = lean_ctor_get(v_a_2087_, 1);
v___x_2108_ = lean_unbox(v_fst_2103_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_unbox(v_fst_2101_);
if (v___x_2109_ == 0)
{
goto v___jp_2105_;
}
else
{
goto v___jp_2096_;
}
}
else
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_unbox(v_fst_2101_);
if (v___x_2110_ == 0)
{
goto v___jp_2096_;
}
else
{
goto v___jp_2105_;
}
}
v___jp_2096_:
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2087_, v_b_2088_, v_tail_2092_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 2, v___x_2097_);
v___x_2099_ = v___x_2094_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_key_2090_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_value_2091_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
v___jp_2105_:
{
uint8_t v___x_2106_; 
v___x_2106_ = l_Lean_ExprStructEq_beq(v_snd_2102_, v_snd_2104_);
if (v___x_2106_ == 0)
{
goto v___jp_2096_;
}
else
{
lean_object* v___x_2107_; 
lean_del_object(v___x_2094_);
lean_dec(v_value_2091_);
lean_dec(v_key_2090_);
v___x_2107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2107_, 0, v_a_2087_);
lean_ctor_set(v___x_2107_, 1, v_b_2088_);
lean_ctor_set(v___x_2107_, 2, v_tail_2092_);
return v___x_2107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
if (lean_obj_tag(v_x_2113_) == 0)
{
return v_x_2112_;
}
else
{
lean_object* v_key_2114_; lean_object* v_value_2115_; lean_object* v_tail_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2147_; 
v_key_2114_ = lean_ctor_get(v_x_2113_, 0);
v_value_2115_ = lean_ctor_get(v_x_2113_, 1);
v_tail_2116_ = lean_ctor_get(v_x_2113_, 2);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2118_ = v_x_2113_;
v_isShared_2119_ = v_isSharedCheck_2147_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_tail_2116_);
lean_inc(v_value_2115_);
lean_inc(v_key_2114_);
lean_dec(v_x_2113_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2147_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_fst_2120_; lean_object* v_snd_2121_; lean_object* v___x_2122_; uint64_t v___y_2124_; uint8_t v___x_2144_; 
v_fst_2120_ = lean_ctor_get(v_key_2114_, 0);
v_snd_2121_ = lean_ctor_get(v_key_2114_, 1);
v___x_2122_ = lean_array_get_size(v_x_2112_);
v___x_2144_ = lean_unbox(v_fst_2120_);
if (v___x_2144_ == 0)
{
uint64_t v___x_2145_; 
v___x_2145_ = 13ULL;
v___y_2124_ = v___x_2145_;
goto v___jp_2123_;
}
else
{
uint64_t v___x_2146_; 
v___x_2146_ = 11ULL;
v___y_2124_ = v___x_2146_;
goto v___jp_2123_;
}
v___jp_2123_:
{
uint64_t v___x_2125_; uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; uint64_t v_fold_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2125_ = l_Lean_ExprStructEq_hash(v_snd_2121_);
v___x_2126_ = lean_uint64_mix_hash(v___y_2124_, v___x_2125_);
v___x_2127_ = 32ULL;
v___x_2128_ = lean_uint64_shift_right(v___x_2126_, v___x_2127_);
v_fold_2129_ = lean_uint64_xor(v___x_2126_, v___x_2128_);
v___x_2130_ = 16ULL;
v___x_2131_ = lean_uint64_shift_right(v_fold_2129_, v___x_2130_);
v___x_2132_ = lean_uint64_xor(v_fold_2129_, v___x_2131_);
v___x_2133_ = lean_uint64_to_usize(v___x_2132_);
v___x_2134_ = lean_usize_of_nat(v___x_2122_);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_sub(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_usize_land(v___x_2133_, v___x_2136_);
v___x_2138_ = lean_array_uget_borrowed(v_x_2112_, v___x_2137_);
lean_inc(v___x_2138_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 2, v___x_2138_);
v___x_2140_ = v___x_2118_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_key_2114_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_value_2115_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_array_uset(v_x_2112_, v___x_2137_, v___x_2140_);
v_x_2112_ = v___x_2141_;
v_x_2113_ = v_tail_2116_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2148_, lean_object* v_source_2149_, lean_object* v_target_2150_){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = lean_array_get_size(v_source_2149_);
v___x_2152_ = lean_nat_dec_lt(v_i_2148_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec_ref(v_source_2149_);
lean_dec(v_i_2148_);
return v_target_2150_;
}
else
{
lean_object* v_es_2153_; lean_object* v___x_2154_; lean_object* v_source_2155_; lean_object* v_target_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_es_2153_ = lean_array_fget(v_source_2149_, v_i_2148_);
v___x_2154_ = lean_box(0);
v_source_2155_ = lean_array_fset(v_source_2149_, v_i_2148_, v___x_2154_);
v_target_2156_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2150_, v_es_2153_);
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_nat_add(v_i_2148_, v___x_2157_);
lean_dec(v_i_2148_);
v_i_2148_ = v___x_2158_;
v_source_2149_ = v_source_2155_;
v_target_2150_ = v_target_2156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2160_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_nbuckets_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2161_ = lean_array_get_size(v_data_2160_);
v___x_2162_ = lean_unsigned_to_nat(2u);
v_nbuckets_2163_ = lean_nat_mul(v___x_2161_, v___x_2162_);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_mk_array(v_nbuckets_2163_, v___x_2165_);
v___x_2167_ = lean_array_propagate_mark(v_data_2160_, v___x_2166_);
v___x_2168_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2164_, v_data_2160_, v___x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2169_, lean_object* v_a_2170_, lean_object* v_b_2171_){
_start:
{
lean_object* v_size_2172_; lean_object* v_buckets_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2224_; 
v_size_2172_ = lean_ctor_get(v_m_2169_, 0);
v_buckets_2173_ = lean_ctor_get(v_m_2169_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_m_2169_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2175_ = v_m_2169_;
v_isShared_2176_ = v_isSharedCheck_2224_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_buckets_2173_);
lean_inc(v_size_2172_);
lean_dec(v_m_2169_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2224_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_fst_2177_; lean_object* v_snd_2178_; lean_object* v___x_2179_; uint64_t v___y_2181_; uint8_t v___x_2221_; 
v_fst_2177_ = lean_ctor_get(v_a_2170_, 0);
v_snd_2178_ = lean_ctor_get(v_a_2170_, 1);
v___x_2179_ = lean_array_get_size(v_buckets_2173_);
v___x_2221_ = lean_unbox(v_fst_2177_);
if (v___x_2221_ == 0)
{
uint64_t v___x_2222_; 
v___x_2222_ = 13ULL;
v___y_2181_ = v___x_2222_;
goto v___jp_2180_;
}
else
{
uint64_t v___x_2223_; 
v___x_2223_ = 11ULL;
v___y_2181_ = v___x_2223_;
goto v___jp_2180_;
}
v___jp_2180_:
{
uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v___x_2184_; uint64_t v___x_2185_; uint64_t v_fold_2186_; uint64_t v___x_2187_; uint64_t v___x_2188_; uint64_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; lean_object* v_bkt_2195_; uint8_t v___x_2196_; 
v___x_2182_ = l_Lean_ExprStructEq_hash(v_snd_2178_);
v___x_2183_ = lean_uint64_mix_hash(v___y_2181_, v___x_2182_);
v___x_2184_ = 32ULL;
v___x_2185_ = lean_uint64_shift_right(v___x_2183_, v___x_2184_);
v_fold_2186_ = lean_uint64_xor(v___x_2183_, v___x_2185_);
v___x_2187_ = 16ULL;
v___x_2188_ = lean_uint64_shift_right(v_fold_2186_, v___x_2187_);
v___x_2189_ = lean_uint64_xor(v_fold_2186_, v___x_2188_);
v___x_2190_ = lean_uint64_to_usize(v___x_2189_);
v___x_2191_ = lean_usize_of_nat(v___x_2179_);
v___x_2192_ = ((size_t)1ULL);
v___x_2193_ = lean_usize_sub(v___x_2191_, v___x_2192_);
v___x_2194_ = lean_usize_land(v___x_2190_, v___x_2193_);
v_bkt_2195_ = lean_array_uget_borrowed(v_buckets_2173_, v___x_2194_);
v___x_2196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2170_, v_bkt_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v_size_x27_2198_; lean_object* v___x_2199_; lean_object* v_buckets_x27_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2197_ = lean_unsigned_to_nat(1u);
v_size_x27_2198_ = lean_nat_add(v_size_2172_, v___x_2197_);
lean_dec(v_size_2172_);
lean_inc(v_bkt_2195_);
v___x_2199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2199_, 0, v_a_2170_);
lean_ctor_set(v___x_2199_, 1, v_b_2171_);
lean_ctor_set(v___x_2199_, 2, v_bkt_2195_);
v_buckets_x27_2200_ = lean_array_uset(v_buckets_2173_, v___x_2194_, v___x_2199_);
v___x_2201_ = lean_unsigned_to_nat(4u);
v___x_2202_ = lean_nat_mul(v_size_x27_2198_, v___x_2201_);
v___x_2203_ = lean_unsigned_to_nat(3u);
v___x_2204_ = lean_nat_div(v___x_2202_, v___x_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_array_get_size(v_buckets_x27_2200_);
v___x_2206_ = lean_nat_dec_le(v___x_2204_, v___x_2205_);
lean_dec(v___x_2204_);
if (v___x_2206_ == 0)
{
lean_object* v_val_2207_; lean_object* v___x_2209_; 
v_val_2207_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2200_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_val_2207_);
lean_ctor_set(v___x_2175_, 0, v_size_x27_2198_);
v___x_2209_ = v___x_2175_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_size_x27_2198_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_val_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
else
{
lean_object* v___x_2212_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_buckets_x27_2200_);
lean_ctor_set(v___x_2175_, 0, v_size_x27_2198_);
v___x_2212_ = v___x_2175_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_size_x27_2198_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_buckets_x27_2200_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v___x_2214_; lean_object* v_buckets_x27_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
lean_inc(v_bkt_2195_);
v___x_2214_ = lean_box(0);
v_buckets_x27_2215_ = lean_array_uset(v_buckets_2173_, v___x_2194_, v___x_2214_);
v___x_2216_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2170_, v_b_2171_, v_bkt_2195_);
v___x_2217_ = lean_array_uset(v_buckets_x27_2215_, v___x_2194_, v___x_2216_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v___x_2217_);
v___x_2219_ = v___x_2175_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_size_2172_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2225_, lean_object* v_x_2226_){
_start:
{
if (lean_obj_tag(v_x_2226_) == 0)
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_box(0);
return v___x_2227_;
}
else
{
lean_object* v_key_2228_; lean_object* v_value_2229_; lean_object* v_tail_2230_; lean_object* v_fst_2231_; lean_object* v_snd_2232_; lean_object* v_fst_2233_; lean_object* v_snd_2234_; uint8_t v___x_2239_; 
v_key_2228_ = lean_ctor_get(v_x_2226_, 0);
v_value_2229_ = lean_ctor_get(v_x_2226_, 1);
v_tail_2230_ = lean_ctor_get(v_x_2226_, 2);
v_fst_2231_ = lean_ctor_get(v_key_2228_, 0);
v_snd_2232_ = lean_ctor_get(v_key_2228_, 1);
v_fst_2233_ = lean_ctor_get(v_a_2225_, 0);
v_snd_2234_ = lean_ctor_get(v_a_2225_, 1);
v___x_2239_ = lean_unbox(v_fst_2233_);
if (v___x_2239_ == 0)
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_unbox(v_fst_2231_);
if (v___x_2240_ == 0)
{
goto v___jp_2235_;
}
else
{
v_x_2226_ = v_tail_2230_;
goto _start;
}
}
else
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_unbox(v_fst_2231_);
if (v___x_2242_ == 0)
{
v_x_2226_ = v_tail_2230_;
goto _start;
}
else
{
goto v___jp_2235_;
}
}
v___jp_2235_:
{
uint8_t v___x_2236_; 
v___x_2236_ = l_Lean_ExprStructEq_beq(v_snd_2232_, v_snd_2234_);
if (v___x_2236_ == 0)
{
v_x_2226_ = v_tail_2230_;
goto _start;
}
else
{
lean_object* v___x_2238_; 
lean_inc(v_value_2229_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v_value_2229_);
return v___x_2238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2244_, lean_object* v_x_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2244_, v_x_2245_);
lean_dec(v_x_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_buckets_2249_; lean_object* v_fst_2250_; lean_object* v_snd_2251_; lean_object* v___x_2252_; uint64_t v___y_2254_; uint8_t v___x_2270_; 
v_buckets_2249_ = lean_ctor_get(v_m_2247_, 1);
v_fst_2250_ = lean_ctor_get(v_a_2248_, 0);
v_snd_2251_ = lean_ctor_get(v_a_2248_, 1);
v___x_2252_ = lean_array_get_size(v_buckets_2249_);
v___x_2270_ = lean_unbox(v_fst_2250_);
if (v___x_2270_ == 0)
{
uint64_t v___x_2271_; 
v___x_2271_ = 13ULL;
v___y_2254_ = v___x_2271_;
goto v___jp_2253_;
}
else
{
uint64_t v___x_2272_; 
v___x_2272_ = 11ULL;
v___y_2254_ = v___x_2272_;
goto v___jp_2253_;
}
v___jp_2253_:
{
uint64_t v___x_2255_; uint64_t v___x_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v_fold_2259_; uint64_t v___x_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2255_ = l_Lean_ExprStructEq_hash(v_snd_2251_);
v___x_2256_ = lean_uint64_mix_hash(v___y_2254_, v___x_2255_);
v___x_2257_ = 32ULL;
v___x_2258_ = lean_uint64_shift_right(v___x_2256_, v___x_2257_);
v_fold_2259_ = lean_uint64_xor(v___x_2256_, v___x_2258_);
v___x_2260_ = 16ULL;
v___x_2261_ = lean_uint64_shift_right(v_fold_2259_, v___x_2260_);
v___x_2262_ = lean_uint64_xor(v_fold_2259_, v___x_2261_);
v___x_2263_ = lean_uint64_to_usize(v___x_2262_);
v___x_2264_ = lean_usize_of_nat(v___x_2252_);
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_sub(v___x_2264_, v___x_2265_);
v___x_2267_ = lean_usize_land(v___x_2263_, v___x_2266_);
v___x_2268_ = lean_array_uget_borrowed(v_buckets_2249_, v___x_2267_);
v___x_2269_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2248_, v___x_2268_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2273_, v_a_2274_);
lean_dec_ref(v_a_2274_);
lean_dec_ref(v_m_2273_);
return v_res_2275_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2276_; lean_object* v_dummy_2277_; 
v___x_2276_ = lean_box(0);
v_dummy_2277_ = l_Lean_Expr_sort___override(v___x_2276_);
return v_dummy_2277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2278_, lean_object* v_fst_2279_, lean_object* v_fvars_2280_, lean_object* v_a_2281_, lean_object* v_b_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_a_2292_; uint8_t v___x_2296_; 
v___x_2296_ = lean_nat_dec_lt(v_a_2281_, v_upperBound_2278_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
lean_dec(v_a_2281_);
lean_dec(v_fvars_2280_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_b_2282_);
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v_binderInfo_2300_; uint8_t v___x_2301_; 
v___x_2298_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2299_ = lean_array_get_borrowed(v___x_2298_, v_fst_2279_, v_a_2281_);
v_binderInfo_2300_ = lean_ctor_get_uint8(v___x_2299_, sizeof(void*)*2);
v___x_2301_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2300_);
if (v___x_2301_ == 0)
{
v_a_2292_ = v_b_2282_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2302_ = l_Lean_instInhabitedExpr;
v___x_2303_ = 0;
v___x_2304_ = lean_array_get_borrowed(v___x_2302_, v_b_2282_, v_a_2281_);
lean_inc(v___x_2304_);
lean_inc(v_fvars_2280_);
v___x_2305_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2280_, v___x_2304_, v___x_2303_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = lean_array_set(v_b_2282_, v_a_2281_, v_a_2306_);
v_a_2292_ = v___x_2307_;
goto v___jp_2291_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_b_2282_);
lean_dec(v_a_2281_);
lean_dec(v_fvars_2280_);
v_a_2308_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2305_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2305_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
v___jp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = lean_nat_add(v_a_2281_, v___x_2293_);
lean_dec(v_a_2281_);
v_a_2281_ = v___x_2294_;
v_b_2282_ = v_a_2292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2316_, size_t v_sz_2317_, size_t v_i_2318_, lean_object* v_bs_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = lean_usize_dec_lt(v_i_2318_, v_sz_2317_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; 
lean_dec(v_fvars_2316_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_bs_2319_);
return v___x_2329_;
}
else
{
uint8_t v___x_2330_; lean_object* v_v_2331_; lean_object* v___x_2332_; lean_object* v_bs_x27_2333_; lean_object* v___x_2334_; 
v___x_2330_ = 0;
v_v_2331_ = lean_array_uget(v_bs_2319_, v_i_2318_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v_bs_x27_2333_ = lean_array_uset(v_bs_2319_, v_i_2318_, v___x_2332_);
lean_inc(v_fvars_2316_);
v___x_2334_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2316_, v_v_2331_, v___x_2330_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = ((size_t)1ULL);
v___x_2337_ = lean_usize_add(v_i_2318_, v___x_2336_);
v___x_2338_ = lean_array_uset(v_bs_x27_2333_, v_i_2318_, v_a_2335_);
v_i_2318_ = v___x_2337_;
v_bs_2319_ = v___x_2338_;
goto _start;
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_bs_x27_2333_);
lean_dec(v_fvars_2316_);
v_a_2340_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2334_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2334_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2348_, lean_object* v_f_2349_, lean_object* v_args_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
uint8_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = 0;
lean_inc_ref(v_f_2349_);
lean_inc(v_fvars_2348_);
v___x_2360_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2348_, v_f_2349_, v___x_2359_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2360_) == 0)
{
uint8_t v_implicits_2361_; 
v_implicits_2361_ = lean_ctor_get_uint8(v_a_2351_, 2);
if (v_implicits_2361_ == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2360_, 1);
lean_inc(v_a_2357_);
lean_inc_ref(v_a_2356_);
lean_inc(v_a_2355_);
lean_inc_ref(v_a_2354_);
v___x_2363_ = lean_infer_type(v_f_2349_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2364_, v_args_2350_, v___x_2359_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v_fst_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v_fst_2367_ = lean_ctor_get(v_a_2366_, 0);
lean_inc(v_fst_2367_);
lean_dec(v_a_2366_);
v___x_2368_ = lean_array_get_size(v_args_2350_);
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2368_, v_fst_2367_, v_fvars_2348_, v___x_2369_, v_args_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
lean_dec(v_fst_2367_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2379_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2379_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2379_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = l_Lean_mkAppN(v_a_2362_, v_a_2371_);
lean_dec(v_a_2371_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2375_);
v___x_2377_ = v___x_2373_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v_a_2362_);
v_a_2380_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2370_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2370_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_a_2362_);
lean_dec_ref(v_args_2350_);
lean_dec(v_fvars_2348_);
v_a_2388_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2365_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2365_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_dec(v_a_2362_);
lean_dec_ref(v_args_2350_);
lean_dec(v_fvars_2348_);
return v___x_2363_;
}
}
else
{
lean_object* v_a_2396_; size_t v_sz_2397_; size_t v___x_2398_; lean_object* v___x_2399_; 
lean_dec_ref(v_f_2349_);
v_a_2396_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2360_, 1);
v_sz_2397_ = lean_array_size(v_args_2350_);
v___x_2398_ = ((size_t)0ULL);
v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2348_, v_sz_2397_, v___x_2398_, v_args_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2408_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = l_Lean_mkAppN(v_a_2396_, v_a_2400_);
lean_dec(v_a_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_a_2396_);
v_a_2409_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2399_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2399_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2350_);
lean_dec_ref(v_f_2349_);
lean_dec(v_fvars_2348_);
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2417_, lean_object* v_f_2418_, lean_object* v_args_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2417_, v_f_2418_, v_args_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2429_, lean_object* v_b_2430_, uint8_t v___x_2431_, lean_object* v_mk_2432_, lean_object* v_a_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_inc_ref(v_x_2434_);
v___x_2443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2443_, 0, v_x_2434_);
lean_ctor_set(v___x_2443_, 1, v_fvars_2429_);
v___x_2444_ = lean_expr_instantiate1(v_b_2430_, v_x_2434_);
v___x_2445_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2443_, v___x_2444_, v___x_2431_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2445_) == 0)
{
uint8_t v_lift_2446_; 
v_lift_2446_ = lean_ctor_get_uint8(v___y_2435_, 10);
if (v_lift_2446_ == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2459_; 
v_a_2447_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2449_ = v___x_2445_;
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2445_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_mk_empty_array_with_capacity(v___x_2451_);
v___x_2453_ = lean_array_push(v___x_2452_, v_x_2434_);
v___x_2454_ = lean_expr_abstract(v_a_2447_, v___x_2453_);
lean_dec_ref(v___x_2453_);
lean_dec(v_a_2447_);
v___x_2455_ = lean_apply_2(v_mk_2432_, v_a_2433_, v___x_2454_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2455_);
v___x_2457_ = v___x_2449_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_a_2460_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2461_ = l_Lean_Expr_fvarId_x21(v_x_2434_);
v___x_2462_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2461_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2476_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2476_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2476_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2467_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2463_, v_a_2460_);
lean_dec(v_a_2463_);
v___x_2468_ = lean_unsigned_to_nat(1u);
v___x_2469_ = lean_mk_empty_array_with_capacity(v___x_2468_);
v___x_2470_ = lean_array_push(v___x_2469_, v_x_2434_);
v___x_2471_ = lean_expr_abstract(v___x_2467_, v___x_2470_);
lean_dec_ref(v___x_2470_);
lean_dec_ref(v___x_2467_);
v___x_2472_ = lean_apply_2(v_mk_2432_, v_a_2433_, v___x_2471_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2472_);
v___x_2474_ = v___x_2465_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_a_2460_);
lean_dec_ref(v_x_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_mk_2432_);
v_a_2477_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2462_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2462_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2434_);
lean_dec_ref(v_a_2433_);
lean_dec_ref(v_mk_2432_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2485_, lean_object* v_b_2486_, lean_object* v___x_2487_, lean_object* v_mk_2488_, lean_object* v_a_2489_, lean_object* v_x_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v___x_41964__boxed_2499_; lean_object* v_res_2500_; 
v___x_41964__boxed_2499_ = lean_unbox(v___x_2487_);
v_res_2500_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2485_, v_b_2486_, v___x_41964__boxed_2499_, v_mk_2488_, v_a_2489_, v_x_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v_b_2486_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2501_, lean_object* v_n_2502_, lean_object* v_t_2503_, lean_object* v_b_2504_, uint8_t v_i_2505_, lean_object* v_mk_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
uint8_t v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = 0;
lean_inc(v_fvars_2501_);
v___x_2516_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2501_, v_t_2503_, v___x_2515_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
if (lean_obj_tag(v___x_2516_) == 0)
{
uint8_t v_underBinder_2517_; 
v_underBinder_2517_ = lean_ctor_get_uint8(v_a_2507_, 4);
if (v_underBinder_2517_ == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_n_2502_);
lean_dec(v_fvars_2501_);
v_a_2518_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v___x_2516_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2516_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_apply_2(v_mk_2506_, v_a_2518_, v_b_2504_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___f_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; 
v_a_2527_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_n(v_a_2527_, 2);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2528_ = lean_box(v___x_2515_);
v___f_2529_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2529_, 0, v_fvars_2501_);
lean_closure_set(v___f_2529_, 1, v_b_2504_);
lean_closure_set(v___f_2529_, 2, v___x_2528_);
lean_closure_set(v___f_2529_, 3, v_mk_2506_);
lean_closure_set(v___f_2529_, 4, v_a_2527_);
v___x_2530_ = 0;
v___x_2531_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2502_, v_i_2505_, v_a_2527_, v___f_2529_, v___x_2530_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
return v___x_2531_;
}
}
else
{
lean_dec_ref(v_mk_2506_);
lean_dec_ref(v_b_2504_);
lean_dec(v_n_2502_);
lean_dec(v_fvars_2501_);
return v___x_2516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2532_, lean_object* v_n_2533_, lean_object* v_t_2534_, lean_object* v_b_2535_, lean_object* v_i_2536_, lean_object* v_mk_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_i_boxed_2546_; lean_object* v_res_2547_; 
v_i_boxed_2546_ = lean_unbox(v_i_2536_);
v_res_2547_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2532_, v_n_2533_, v_t_2534_, v_b_2535_, v_i_boxed_2546_, v_mk_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2548_, lean_object* v_e_2549_, lean_object* v_topLevel_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
uint8_t v_topLevel_boxed_2559_; lean_object* v_res_2560_; 
v_topLevel_boxed_2559_ = lean_unbox(v_topLevel_2550_);
v_res_2560_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2548_, v_e_2549_, v_topLevel_boxed_2559_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
return v_res_2560_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2565_ = lean_unsigned_to_nat(27u);
v___x_2566_ = lean_unsigned_to_nat(1964u);
v___x_2567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2569_ = l_mkPanicMessageWithDecl(v___x_2568_, v___x_2567_, v___x_2566_, v___x_2565_, v___x_2564_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2570_, lean_object* v_fvars_2571_, lean_object* v_b_2572_, uint8_t v___x_2573_, lean_object* v_e_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, uint8_t v_isLet_2577_, uint8_t v_topLevel_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
if (v_fst_2570_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_inc_ref(v_x_2579_);
v___x_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_x_2579_);
lean_ctor_set(v___x_2588_, 1, v_fvars_2571_);
v___x_2589_ = lean_expr_instantiate1(v_b_2572_, v_x_2579_);
v___x_2590_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2588_, v___x_2589_, v___x_2573_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
if (lean_obj_tag(v___x_2590_) == 0)
{
if (lean_obj_tag(v_e_2574_) == 8)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2628_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2628_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2628_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_declName_2595_; lean_object* v_type_2596_; lean_object* v_value_2597_; lean_object* v_body_2598_; uint8_t v_nondep_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; uint8_t v___x_2606_; 
v_declName_2595_ = lean_ctor_get(v_e_2574_, 0);
v_type_2596_ = lean_ctor_get(v_e_2574_, 1);
v_value_2597_ = lean_ctor_get(v_e_2574_, 2);
v_body_2598_ = lean_ctor_get(v_e_2574_, 3);
v_nondep_2599_ = lean_ctor_get_uint8(v_e_2574_, sizeof(void*)*4 + 8);
v___x_2600_ = lean_unsigned_to_nat(1u);
v___x_2601_ = lean_mk_empty_array_with_capacity(v___x_2600_);
v___x_2602_ = lean_array_push(v___x_2601_, v_x_2579_);
v___x_2603_ = lean_expr_abstract(v_a_2591_, v___x_2602_);
lean_dec_ref(v___x_2602_);
lean_dec(v_a_2591_);
v___x_2604_ = lean_ptr_addr(v_type_2596_);
v___x_2605_ = lean_ptr_addr(v_a_2575_);
v___x_2606_ = lean_usize_dec_eq(v___x_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_inc(v_declName_2595_);
lean_dec_ref_known(v_e_2574_, 4);
v___x_2607_ = l_Lean_Expr_letE___override(v_declName_2595_, v_a_2575_, v_a_2576_, v___x_2603_, v_nondep_2599_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2607_);
v___x_2609_ = v___x_2593_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
else
{
size_t v___x_2611_; size_t v___x_2612_; uint8_t v___x_2613_; 
v___x_2611_ = lean_ptr_addr(v_value_2597_);
v___x_2612_ = lean_ptr_addr(v_a_2576_);
v___x_2613_ = lean_usize_dec_eq(v___x_2611_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_inc(v_declName_2595_);
lean_dec_ref_known(v_e_2574_, 4);
v___x_2614_ = l_Lean_Expr_letE___override(v_declName_2595_, v_a_2575_, v_a_2576_, v___x_2603_, v_nondep_2599_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2614_);
v___x_2616_ = v___x_2593_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
else
{
size_t v___x_2618_; size_t v___x_2619_; uint8_t v___x_2620_; 
v___x_2618_ = lean_ptr_addr(v_body_2598_);
v___x_2619_ = lean_ptr_addr(v___x_2603_);
v___x_2620_ = lean_usize_dec_eq(v___x_2618_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_inc(v_declName_2595_);
lean_dec_ref_known(v_e_2574_, 4);
v___x_2621_ = l_Lean_Expr_letE___override(v_declName_2595_, v_a_2575_, v_a_2576_, v___x_2603_, v_nondep_2599_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2621_);
v___x_2623_ = v___x_2593_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
else
{
lean_object* v___x_2626_; 
lean_dec_ref(v___x_2603_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_a_2575_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v_e_2574_);
v___x_2626_ = v___x_2593_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_e_2574_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
else
{
lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_x_2579_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec_ref(v_e_2574_);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2590_, 0);
lean_dec(v_unused_2638_);
v___x_2630_ = v___x_2590_;
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
else
{
lean_dec(v___x_2590_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2633_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2632_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2633_);
v___x_2635_ = v___x_2630_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_dec_ref(v_x_2579_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec_ref(v_e_2574_);
return v___x_2590_;
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec_ref(v_e_2574_);
v___x_2639_ = l_Lean_Expr_fvarId_x21(v_x_2579_);
v___x_2640_ = l_Lean_FVarId_getDecl___redArg(v___x_2639_, v___y_2583_, v___y_2585_, v___y_2586_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2641_, v_isLet_2577_, v___y_2580_, v___y_2582_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec_ref_known(v___x_2642_, 1);
v___x_2643_ = lean_expr_instantiate1(v_b_2572_, v_x_2579_);
lean_dec_ref(v_x_2579_);
v___x_2644_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2571_, v___x_2643_, v_topLevel_2578_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2644_;
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v_x_2579_);
lean_dec(v_fvars_2571_);
v_a_2645_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2642_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2642_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v_x_2579_);
lean_dec(v_fvars_2571_);
v_a_2653_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2640_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2640_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2661_ = _args[0];
lean_object* v_fvars_2662_ = _args[1];
lean_object* v_b_2663_ = _args[2];
lean_object* v___x_2664_ = _args[3];
lean_object* v_e_2665_ = _args[4];
lean_object* v_a_2666_ = _args[5];
lean_object* v_a_2667_ = _args[6];
lean_object* v_isLet_2668_ = _args[7];
lean_object* v_topLevel_2669_ = _args[8];
lean_object* v_x_2670_ = _args[9];
lean_object* v___y_2671_ = _args[10];
lean_object* v___y_2672_ = _args[11];
lean_object* v___y_2673_ = _args[12];
lean_object* v___y_2674_ = _args[13];
lean_object* v___y_2675_ = _args[14];
lean_object* v___y_2676_ = _args[15];
lean_object* v___y_2677_ = _args[16];
lean_object* v___y_2678_ = _args[17];
_start:
{
uint8_t v_fst_42109__boxed_2679_; uint8_t v___x_42110__boxed_2680_; uint8_t v_isLet_boxed_2681_; uint8_t v_topLevel_boxed_2682_; lean_object* v_res_2683_; 
v_fst_42109__boxed_2679_ = lean_unbox(v_fst_2661_);
v___x_42110__boxed_2680_ = lean_unbox(v___x_2664_);
v_isLet_boxed_2681_ = lean_unbox(v_isLet_2668_);
v_topLevel_boxed_2682_ = lean_unbox(v_topLevel_2669_);
v_res_2683_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_42109__boxed_2679_, v_fvars_2662_, v_b_2663_, v___x_42110__boxed_2680_, v_e_2665_, v_a_2666_, v_a_2667_, v_isLet_boxed_2681_, v_topLevel_boxed_2682_, v_x_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v_b_2663_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2684_, lean_object* v_e_2685_, uint8_t v_isLet_2686_, lean_object* v_n_2687_, lean_object* v_t_2688_, lean_object* v_v_2689_, lean_object* v_b_2690_, uint8_t v_topLevel_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; uint8_t v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = 0;
lean_inc(v_fvars_2684_);
v___x_2715_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2684_, v_t_2688_, v___x_2714_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
lean_inc(v_fvars_2684_);
v___x_2717_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2684_, v_v_2689_, v___x_2714_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2829_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2829_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2829_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; uint8_t v_descend_2769_; uint8_t v_underBinder_2770_; uint8_t v_usedOnly_2771_; uint8_t v_merge_2772_; uint8_t v_lift_2773_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; uint8_t v___y_2811_; 
v_descend_2769_ = lean_ctor_get_uint8(v_a_2692_, 3);
v_underBinder_2770_ = lean_ctor_get_uint8(v_a_2692_, 4);
v_usedOnly_2771_ = lean_ctor_get_uint8(v_a_2692_, 5);
v_merge_2772_ = lean_ctor_get_uint8(v_a_2692_, 6);
v_lift_2773_ = lean_ctor_get_uint8(v_a_2692_, 10);
if (v_usedOnly_2771_ == 0)
{
v___y_2811_ = v___x_2714_;
goto v___jp_2810_;
}
else
{
uint8_t v___x_2827_; 
v___x_2827_ = l_Lean_Expr_hasLooseBVars(v_b_2690_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_del_object(v___x_2720_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_n_2687_);
lean_dec_ref(v_e_2685_);
v___x_2828_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2684_, v_b_2690_, v_topLevel_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
return v___x_2828_;
}
else
{
v___y_2811_ = v___x_2714_;
goto v___jp_2810_;
}
}
v___jp_2722_:
{
if (lean_obj_tag(v_e_2685_) == 8)
{
lean_object* v_declName_2723_; lean_object* v_type_2724_; lean_object* v_value_2725_; lean_object* v_body_2726_; uint8_t v_nondep_2727_; size_t v___x_2728_; size_t v___x_2729_; uint8_t v___x_2730_; 
v_declName_2723_ = lean_ctor_get(v_e_2685_, 0);
v_type_2724_ = lean_ctor_get(v_e_2685_, 1);
v_value_2725_ = lean_ctor_get(v_e_2685_, 2);
v_body_2726_ = lean_ctor_get(v_e_2685_, 3);
v_nondep_2727_ = lean_ctor_get_uint8(v_e_2685_, sizeof(void*)*4 + 8);
v___x_2728_ = lean_ptr_addr(v_type_2724_);
v___x_2729_ = lean_ptr_addr(v_a_2716_);
v___x_2730_ = lean_usize_dec_eq(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_inc(v_declName_2723_);
lean_dec_ref_known(v_e_2685_, 4);
v___x_2731_ = l_Lean_Expr_letE___override(v_declName_2723_, v_a_2716_, v_a_2718_, v_b_2690_, v_nondep_2727_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2731_);
v___x_2733_ = v___x_2720_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
else
{
size_t v___x_2735_; size_t v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = lean_ptr_addr(v_value_2725_);
v___x_2736_ = lean_ptr_addr(v_a_2718_);
v___x_2737_ = lean_usize_dec_eq(v___x_2735_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_inc(v_declName_2723_);
lean_dec_ref_known(v_e_2685_, 4);
v___x_2738_ = l_Lean_Expr_letE___override(v_declName_2723_, v_a_2716_, v_a_2718_, v_b_2690_, v_nondep_2727_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2738_);
v___x_2740_ = v___x_2720_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
else
{
size_t v___x_2742_; size_t v___x_2743_; uint8_t v___x_2744_; 
v___x_2742_ = lean_ptr_addr(v_body_2726_);
v___x_2743_ = lean_ptr_addr(v_b_2690_);
v___x_2744_ = lean_usize_dec_eq(v___x_2742_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_inc(v_declName_2723_);
lean_dec_ref_known(v_e_2685_, 4);
v___x_2745_ = l_Lean_Expr_letE___override(v_declName_2723_, v_a_2716_, v_a_2718_, v_b_2690_, v_nondep_2727_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2745_);
v___x_2747_ = v___x_2720_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
else
{
lean_object* v___x_2750_; 
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec_ref(v_b_2690_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v_e_2685_);
v___x_2750_ = v___x_2720_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_e_2685_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec_ref(v_b_2690_);
lean_dec_ref(v_e_2685_);
v___x_2752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2753_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2752_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2753_);
v___x_2755_ = v___x_2720_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
v___jp_2757_:
{
uint8_t v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = 0;
v___x_2768_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2763_, v_a_2716_, v_a_2718_, v___y_2762_, v___x_2714_, v___x_2767_, v___y_2758_, v___y_2765_, v___y_2759_, v___y_2760_, v___y_2764_, v___y_2761_, v___y_2766_);
return v___x_2768_;
}
v___jp_2774_:
{
if (v_underBinder_2770_ == 0)
{
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
goto v___jp_2722_;
}
else
{
if (v_descend_2769_ == 0)
{
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
goto v___jp_2722_;
}
else
{
lean_del_object(v___x_2720_);
lean_dec_ref(v_b_2690_);
lean_dec_ref(v_e_2685_);
v___y_2758_ = v___y_2775_;
v___y_2759_ = v___y_2776_;
v___y_2760_ = v___y_2777_;
v___y_2761_ = v___y_2778_;
v___y_2762_ = v___y_2780_;
v___y_2763_ = v___y_2779_;
v___y_2764_ = v___y_2781_;
v___y_2765_ = v___y_2782_;
v___y_2766_ = v___y_2783_;
goto v___jp_2757_;
}
}
}
v___jp_2784_:
{
lean_object* v___x_2793_; 
lean_inc(v_a_2718_);
lean_inc(v_a_2716_);
v___x_2793_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2684_, v_n_2687_, v_a_2716_, v_a_2718_, v___y_2786_, v___y_2788_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v_fst_2795_; lean_object* v_snd_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___f_2800_; uint8_t v___x_2801_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v_fst_2795_ = lean_ctor_get(v_a_2794_, 0);
lean_inc_n(v_fst_2795_, 2);
v_snd_2796_ = lean_ctor_get(v_a_2794_, 1);
lean_inc(v_snd_2796_);
lean_dec(v_a_2794_);
v___x_2797_ = lean_box(v___x_2714_);
v___x_2798_ = lean_box(v_isLet_2686_);
v___x_2799_ = lean_box(v_topLevel_2691_);
lean_inc(v_a_2718_);
lean_inc(v_a_2716_);
lean_inc_ref(v_e_2685_);
lean_inc_ref(v_b_2690_);
v___f_2800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2800_, 0, v_fst_2795_);
lean_closure_set(v___f_2800_, 1, v_fvars_2684_);
lean_closure_set(v___f_2800_, 2, v_b_2690_);
lean_closure_set(v___f_2800_, 3, v___x_2797_);
lean_closure_set(v___f_2800_, 4, v_e_2685_);
lean_closure_set(v___f_2800_, 5, v_a_2716_);
lean_closure_set(v___f_2800_, 6, v_a_2718_);
lean_closure_set(v___f_2800_, 7, v___x_2798_);
lean_closure_set(v___f_2800_, 8, v___x_2799_);
v___x_2801_ = lean_unbox(v_fst_2795_);
lean_dec(v_fst_2795_);
if (v___x_2801_ == 0)
{
v___y_2775_ = v___y_2786_;
v___y_2776_ = v___y_2788_;
v___y_2777_ = v___y_2789_;
v___y_2778_ = v___y_2791_;
v___y_2779_ = v_snd_2796_;
v___y_2780_ = v___f_2800_;
v___y_2781_ = v___y_2790_;
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2792_;
goto v___jp_2774_;
}
else
{
if (v___y_2785_ == 0)
{
lean_del_object(v___x_2720_);
lean_dec_ref(v_b_2690_);
lean_dec_ref(v_e_2685_);
v___y_2758_ = v___y_2786_;
v___y_2759_ = v___y_2788_;
v___y_2760_ = v___y_2789_;
v___y_2761_ = v___y_2791_;
v___y_2762_ = v___f_2800_;
v___y_2763_ = v_snd_2796_;
v___y_2764_ = v___y_2790_;
v___y_2765_ = v___y_2787_;
v___y_2766_ = v___y_2792_;
goto v___jp_2757_;
}
else
{
v___y_2775_ = v___y_2786_;
v___y_2776_ = v___y_2788_;
v___y_2777_ = v___y_2789_;
v___y_2778_ = v___y_2791_;
v___y_2779_ = v_snd_2796_;
v___y_2780_ = v___f_2800_;
v___y_2781_ = v___y_2790_;
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2792_;
goto v___jp_2774_;
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_del_object(v___x_2720_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec_ref(v_b_2690_);
lean_dec_ref(v_e_2685_);
lean_dec(v_fvars_2684_);
v_a_2802_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2793_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2793_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
v___jp_2810_:
{
if (v_merge_2772_ == 0)
{
v___y_2785_ = v___y_2811_;
v___y_2786_ = v_a_2692_;
v___y_2787_ = v_a_2693_;
v___y_2788_ = v_a_2694_;
v___y_2789_ = v_a_2695_;
v___y_2790_ = v_a_2696_;
v___y_2791_ = v_a_2697_;
v___y_2792_ = v_a_2698_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2812_; lean_object* v_valueMap_2813_; lean_object* v___x_2814_; 
v___x_2812_ = lean_st_ref_get(v_a_2694_);
v_valueMap_2813_ = lean_ctor_get(v___x_2812_, 2);
lean_inc_ref(v_valueMap_2813_);
lean_dec(v___x_2812_);
v___x_2814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2813_, v_a_2718_);
lean_dec_ref(v_valueMap_2813_);
if (lean_obj_tag(v___x_2814_) == 1)
{
lean_del_object(v___x_2720_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_n_2687_);
lean_dec_ref(v_e_2685_);
if (v_isLet_2686_ == 0)
{
lean_object* v_val_2815_; 
v_val_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_val_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___y_2701_ = v_val_2815_;
v___y_2702_ = v_a_2692_;
v___y_2703_ = v_a_2693_;
v___y_2704_ = v_a_2694_;
v___y_2705_ = v_a_2695_;
v___y_2706_ = v_a_2696_;
v___y_2707_ = v_a_2697_;
v___y_2708_ = v_a_2698_;
goto v___jp_2700_;
}
else
{
if (v_lift_2773_ == 0)
{
lean_object* v_val_2816_; 
v_val_2816_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v___x_2814_, 1);
v___y_2701_ = v_val_2816_;
v___y_2702_ = v_a_2692_;
v___y_2703_ = v_a_2693_;
v___y_2704_ = v_a_2694_;
v___y_2705_ = v_a_2695_;
v___y_2706_ = v_a_2696_;
v___y_2707_ = v_a_2697_;
v___y_2708_ = v_a_2698_;
goto v___jp_2700_;
}
else
{
lean_object* v_val_2817_; lean_object* v___x_2818_; 
v_val_2817_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2818_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2817_, v_a_2694_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_dec_ref_known(v___x_2818_, 1);
v___y_2701_ = v_val_2817_;
v___y_2702_ = v_a_2692_;
v___y_2703_ = v_a_2693_;
v___y_2704_ = v_a_2694_;
v___y_2705_ = v_a_2695_;
v___y_2706_ = v_a_2696_;
v___y_2707_ = v_a_2697_;
v___y_2708_ = v_a_2698_;
goto v___jp_2700_;
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_val_2817_);
lean_dec_ref(v_b_2690_);
lean_dec(v_fvars_2684_);
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2814_);
v___y_2785_ = v___y_2811_;
v___y_2786_ = v_a_2692_;
v___y_2787_ = v_a_2693_;
v___y_2788_ = v_a_2694_;
v___y_2789_ = v_a_2695_;
v___y_2790_ = v_a_2696_;
v___y_2791_ = v_a_2697_;
v___y_2792_ = v_a_2698_;
goto v___jp_2784_;
}
}
}
}
}
else
{
lean_dec(v_a_2716_);
lean_dec_ref(v_b_2690_);
lean_dec(v_n_2687_);
lean_dec_ref(v_e_2685_);
lean_dec(v_fvars_2684_);
return v___x_2717_;
}
}
else
{
lean_dec_ref(v_b_2690_);
lean_dec_ref(v_v_2689_);
lean_dec(v_n_2687_);
lean_dec_ref(v_e_2685_);
lean_dec(v_fvars_2684_);
return v___x_2715_;
}
v___jp_2700_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_inc(v___y_2701_);
v___x_2709_ = l_Lean_Expr_fvar___override(v___y_2701_);
v___x_2710_ = lean_expr_instantiate1(v_b_2690_, v___x_2709_);
lean_dec_ref(v___x_2709_);
lean_dec_ref(v_b_2690_);
v___x_2711_ = lean_box(v_topLevel_2691_);
v___x_2712_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2712_, 0, v_fvars_2684_);
lean_closure_set(v___x_2712_, 1, v___x_2710_);
lean_closure_set(v___x_2712_, 2, v___x_2711_);
v___x_2713_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2701_, v___x_2712_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2701_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2830_, lean_object* v_struct_2831_, lean_object* v___y_2832_, lean_object* v_typeName_2833_, lean_object* v_idx_2834_, lean_object* v_e_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
uint8_t v___y_41885__boxed_2844_; lean_object* v_res_2845_; 
v___y_41885__boxed_2844_ = lean_unbox(v___y_2832_);
v_res_2845_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2830_, v_struct_2831_, v___y_41885__boxed_2844_, v_typeName_2833_, v_idx_2834_, v_e_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2845_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2849_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2850_ = lean_unsigned_to_nat(75u);
v___x_2851_ = lean_unsigned_to_nat(229u);
v___x_2852_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2853_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2854_ = l_mkPanicMessageWithDecl(v___x_2853_, v___x_2852_, v___x_2851_, v___x_2850_, v___x_2849_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2855_, lean_object* v_e_2856_, lean_object* v_fvars_2857_, uint8_t v___x_2858_, uint8_t v_topLevel_2859_, uint8_t v___y_2860_, lean_object* v_____r_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_k_2871_; 
switch(lean_obj_tag(v_e_2856_))
{
case 5:
{
lean_object* v___x_2874_; lean_object* v_dummy_2875_; lean_object* v_nargs_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2874_ = l_Lean_Expr_getAppFn(v_e_2856_);
v_dummy_2875_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2876_ = l_Lean_Expr_getAppNumArgs(v_e_2856_);
lean_inc(v_nargs_2876_);
v___x_2877_ = lean_mk_array(v_nargs_2876_, v_dummy_2875_);
v___x_2878_ = lean_unsigned_to_nat(1u);
v___x_2879_ = lean_nat_sub(v_nargs_2876_, v___x_2878_);
lean_dec(v_nargs_2876_);
lean_inc_ref(v_e_2856_);
v___x_2880_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2856_, v___x_2877_, v___x_2879_);
v___x_2881_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2881_, 0, v_fvars_2857_);
lean_closure_set(v___x_2881_, 1, v___x_2874_);
lean_closure_set(v___x_2881_, 2, v___x_2880_);
v_k_2871_ = v___x_2881_;
goto v___jp_2870_;
}
case 6:
{
lean_object* v_binderName_2882_; lean_object* v_binderType_2883_; lean_object* v_body_2884_; uint8_t v_binderInfo_2885_; lean_object* v___x_2886_; lean_object* v___f_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_binderName_2882_ = lean_ctor_get(v_e_2856_, 0);
v_binderType_2883_ = lean_ctor_get(v_e_2856_, 1);
v_body_2884_ = lean_ctor_get(v_e_2856_, 2);
v_binderInfo_2885_ = lean_ctor_get_uint8(v_e_2856_, sizeof(void*)*3 + 8);
v___x_2886_ = lean_box(v_binderInfo_2885_);
lean_inc_ref(v_e_2856_);
lean_inc_ref_n(v_body_2884_, 2);
lean_inc_n(v_binderName_2882_, 2);
lean_inc_ref_n(v_binderType_2883_, 2);
v___f_2887_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2887_, 0, v_binderType_2883_);
lean_closure_set(v___f_2887_, 1, v_binderName_2882_);
lean_closure_set(v___f_2887_, 2, v___x_2886_);
lean_closure_set(v___f_2887_, 3, v_body_2884_);
lean_closure_set(v___f_2887_, 4, v_e_2856_);
v___x_2888_ = lean_box(v_binderInfo_2885_);
v___x_2889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2889_, 0, v_fvars_2857_);
lean_closure_set(v___x_2889_, 1, v_binderName_2882_);
lean_closure_set(v___x_2889_, 2, v_binderType_2883_);
lean_closure_set(v___x_2889_, 3, v_body_2884_);
lean_closure_set(v___x_2889_, 4, v___x_2888_);
lean_closure_set(v___x_2889_, 5, v___f_2887_);
v_k_2871_ = v___x_2889_;
goto v___jp_2870_;
}
case 7:
{
lean_object* v_binderName_2890_; lean_object* v_binderType_2891_; lean_object* v_body_2892_; uint8_t v_binderInfo_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_binderName_2890_ = lean_ctor_get(v_e_2856_, 0);
v_binderType_2891_ = lean_ctor_get(v_e_2856_, 1);
v_body_2892_ = lean_ctor_get(v_e_2856_, 2);
v_binderInfo_2893_ = lean_ctor_get_uint8(v_e_2856_, sizeof(void*)*3 + 8);
v___x_2894_ = lean_box(v_binderInfo_2893_);
lean_inc_ref(v_e_2856_);
lean_inc_ref_n(v_body_2892_, 2);
lean_inc_n(v_binderName_2890_, 2);
lean_inc_ref_n(v_binderType_2891_, 2);
v___f_2895_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2895_, 0, v_binderType_2891_);
lean_closure_set(v___f_2895_, 1, v_binderName_2890_);
lean_closure_set(v___f_2895_, 2, v___x_2894_);
lean_closure_set(v___f_2895_, 3, v_body_2892_);
lean_closure_set(v___f_2895_, 4, v_e_2856_);
v___x_2896_ = lean_box(v_binderInfo_2893_);
v___x_2897_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2897_, 0, v_fvars_2857_);
lean_closure_set(v___x_2897_, 1, v_binderName_2890_);
lean_closure_set(v___x_2897_, 2, v_binderType_2891_);
lean_closure_set(v___x_2897_, 3, v_body_2892_);
lean_closure_set(v___x_2897_, 4, v___x_2896_);
lean_closure_set(v___x_2897_, 5, v___f_2895_);
v_k_2871_ = v___x_2897_;
goto v___jp_2870_;
}
case 8:
{
uint8_t v_nondep_2898_; 
v_nondep_2898_ = lean_ctor_get_uint8(v_e_2856_, sizeof(void*)*4 + 8);
if (v_nondep_2898_ == 0)
{
lean_object* v_declName_2899_; lean_object* v_type_2900_; lean_object* v_value_2901_; lean_object* v_body_2902_; lean_object* v___x_2903_; 
v_declName_2899_ = lean_ctor_get(v_e_2856_, 0);
lean_inc(v_declName_2899_);
v_type_2900_ = lean_ctor_get(v_e_2856_, 1);
lean_inc_ref(v_type_2900_);
v_value_2901_ = lean_ctor_get(v_e_2856_, 2);
lean_inc_ref(v_value_2901_);
v_body_2902_ = lean_ctor_get(v_e_2856_, 3);
lean_inc_ref(v_body_2902_);
v___x_2903_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2857_, v_e_2856_, v___x_2858_, v_declName_2899_, v_type_2900_, v_value_2901_, v_body_2902_, v_topLevel_2859_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2903_;
}
else
{
lean_object* v_declName_2904_; lean_object* v_type_2905_; lean_object* v_value_2906_; lean_object* v_body_2907_; lean_object* v___x_2908_; 
v_declName_2904_ = lean_ctor_get(v_e_2856_, 0);
lean_inc(v_declName_2904_);
v_type_2905_ = lean_ctor_get(v_e_2856_, 1);
lean_inc_ref(v_type_2905_);
v_value_2906_ = lean_ctor_get(v_e_2856_, 2);
lean_inc_ref(v_value_2906_);
v_body_2907_ = lean_ctor_get(v_e_2856_, 3);
lean_inc_ref(v_body_2907_);
v___x_2908_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2857_, v_e_2856_, v___y_2860_, v_declName_2904_, v_type_2905_, v_value_2906_, v_body_2907_, v_topLevel_2859_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2908_;
}
}
case 10:
{
lean_object* v_data_2909_; lean_object* v_expr_2910_; lean_object* v___x_2911_; 
v_data_2909_ = lean_ctor_get(v_e_2856_, 0);
v_expr_2910_ = lean_ctor_get(v_e_2856_, 1);
lean_inc_ref(v_expr_2910_);
v___x_2911_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2857_, v_expr_2910_, v_topLevel_2859_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2926_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2926_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2926_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
size_t v___x_2916_; size_t v___x_2917_; uint8_t v___x_2918_; 
v___x_2916_ = lean_ptr_addr(v_expr_2910_);
v___x_2917_ = lean_ptr_addr(v_a_2912_);
v___x_2918_ = lean_usize_dec_eq(v___x_2916_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
lean_inc(v_data_2909_);
lean_dec_ref_known(v_e_2856_, 2);
v___x_2919_ = l_Lean_Expr_mdata___override(v_data_2909_, v_a_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2919_);
v___x_2921_ = v___x_2914_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
else
{
lean_object* v___x_2924_; 
lean_dec(v_a_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v_e_2856_);
v___x_2924_ = v___x_2914_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_e_2856_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2856_, 2);
return v___x_2911_;
}
}
case 11:
{
lean_object* v_typeName_2927_; lean_object* v_idx_2928_; lean_object* v_struct_2929_; lean_object* v___x_2930_; lean_object* v___f_2931_; 
v_typeName_2927_ = lean_ctor_get(v_e_2856_, 0);
v_idx_2928_ = lean_ctor_get(v_e_2856_, 1);
v_struct_2929_ = lean_ctor_get(v_e_2856_, 2);
v___x_2930_ = lean_box(v___y_2860_);
lean_inc_ref(v_e_2856_);
lean_inc(v_idx_2928_);
lean_inc(v_typeName_2927_);
lean_inc_ref(v_struct_2929_);
v___f_2931_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2931_, 0, v_fvars_2857_);
lean_closure_set(v___f_2931_, 1, v_struct_2929_);
lean_closure_set(v___f_2931_, 2, v___x_2930_);
lean_closure_set(v___f_2931_, 3, v_typeName_2927_);
lean_closure_set(v___f_2931_, 4, v_idx_2928_);
lean_closure_set(v___f_2931_, 5, v_e_2856_);
v_k_2871_ = v___f_2931_;
goto v___jp_2870_;
}
default: 
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v_fvars_2857_);
lean_dec_ref(v_e_2856_);
v___x_2932_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2933_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2932_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2933_;
}
}
v___jp_2870_:
{
if (v_descend_2855_ == 0)
{
lean_object* v___x_2872_; 
lean_dec_ref(v_k_2871_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_e_2856_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; 
lean_dec_ref(v_e_2856_);
lean_inc(v___y_2868_);
lean_inc_ref(v___y_2867_);
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
lean_inc(v___y_2864_);
lean_inc(v___y_2863_);
lean_inc_ref(v___y_2862_);
v___x_2873_ = lean_apply_8(v_k_2871_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, lean_box(0));
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2934_, lean_object* v_e_2935_, lean_object* v_fvars_2936_, lean_object* v___x_2937_, lean_object* v_topLevel_2938_, lean_object* v___y_2939_, lean_object* v_____r_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v_descend_boxed_2949_; uint8_t v___x_42038__boxed_2950_; uint8_t v_topLevel_boxed_2951_; uint8_t v___y_42039__boxed_2952_; lean_object* v_res_2953_; 
v_descend_boxed_2949_ = lean_unbox(v_descend_2934_);
v___x_42038__boxed_2950_ = lean_unbox(v___x_2937_);
v_topLevel_boxed_2951_ = lean_unbox(v_topLevel_2938_);
v___y_42039__boxed_2952_ = lean_unbox(v___y_2939_);
v_res_2953_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2949_, v_e_2935_, v_fvars_2936_, v___x_42038__boxed_2950_, v_topLevel_boxed_2951_, v___y_42039__boxed_2952_, v_____r_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_2954_, lean_object* v_e_2955_, uint8_t v_topLevel_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v___y_2966_; lean_object* v_a_2967_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2977_; lean_object* v___y_2978_; uint8_t v___x_2981_; 
v___x_2981_ = l_Lean_Expr_isAtomic(v_e_2955_);
if (v___x_2981_ == 0)
{
uint8_t v_proofs_2982_; uint8_t v_types_2983_; uint8_t v_descend_2984_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; uint8_t v___y_2989_; uint8_t v___y_3006_; 
v_proofs_2982_ = lean_ctor_get_uint8(v_a_2957_, 0);
v_types_2983_ = lean_ctor_get_uint8(v_a_2957_, 1);
v_descend_2984_ = lean_ctor_get_uint8(v_a_2957_, 3);
if (v_descend_2984_ == 0)
{
goto v___jp_3030_;
}
else
{
if (v___x_2981_ == 0)
{
v___y_3006_ = v___x_2981_;
goto v___jp_3005_;
}
else
{
goto v___jp_3030_;
}
}
v___jp_2985_:
{
if (v___y_2989_ == 0)
{
lean_dec_ref(v___y_2987_);
if (v_proofs_2982_ == 0)
{
lean_object* v___x_2990_; 
lean_inc_ref(v_e_2955_);
v___x_2990_ = l_Lean_Meta_isProof(v_e_2955_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; uint8_t v___x_2992_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = lean_unbox(v_a_2991_);
lean_dec(v_a_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_dec_ref(v_e_2955_);
v___x_2993_ = lean_box(0);
lean_inc(v_a_2963_);
lean_inc_ref(v_a_2962_);
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc(v_a_2958_);
lean_inc_ref(v_a_2957_);
v___x_2994_ = lean_apply_9(v___y_2988_, v___x_2993_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, lean_box(0));
v___y_2973_ = v___y_2986_;
v___y_2974_ = v___x_2994_;
goto v___jp_2972_;
}
else
{
lean_dec_ref(v___y_2988_);
v___y_2966_ = v___y_2986_;
v_a_2967_ = v_e_2955_;
goto v___jp_2965_;
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2986_);
lean_dec_ref(v_e_2955_);
v_a_2995_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2990_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2990_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec_ref(v_e_2955_);
v___x_3003_ = lean_box(0);
lean_inc(v_a_2963_);
lean_inc_ref(v_a_2962_);
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc(v_a_2958_);
lean_inc_ref(v_a_2957_);
v___x_3004_ = lean_apply_9(v___y_2988_, v___x_3003_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, lean_box(0));
v___y_2973_ = v___y_2986_;
v___y_2974_ = v___x_3004_;
goto v___jp_2972_;
}
}
else
{
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_e_2955_);
v___y_2977_ = v___y_2986_;
v___y_2978_ = v___y_2987_;
goto v___jp_2976_;
}
}
v___jp_3005_:
{
if (v___y_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3007_ = lean_box(v_topLevel_2956_);
lean_inc_ref(v_e_2955_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v_e_2955_);
v___x_3009_ = lean_st_ref_get(v_a_2958_);
v___x_3010_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3009_, v___x_3008_);
lean_dec(v___x_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
uint8_t v___x_3011_; 
v___x_3011_ = l_Lean_Meta_ExtractLets_containsLet(v_e_2955_);
if (v___x_3011_ == 0)
{
lean_dec(v_fvars_2954_);
v___y_2966_ = v___x_3008_;
v_a_2967_ = v_e_2955_;
goto v___jp_2965_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; lean_object* v___f_3018_; 
v___x_3012_ = lean_box(v_descend_2984_);
v___x_3013_ = lean_box(v___x_3011_);
v___x_3014_ = lean_box(v_topLevel_2956_);
v___x_3015_ = lean_box(v___y_3006_);
lean_inc_ref_n(v_e_2955_, 2);
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3016_, 0, v___x_3012_);
lean_closure_set(v___f_3016_, 1, v_e_2955_);
lean_closure_set(v___f_3016_, 2, v_fvars_2954_);
lean_closure_set(v___f_3016_, 3, v___x_3013_);
lean_closure_set(v___f_3016_, 4, v___x_3014_);
lean_closure_set(v___f_3016_, 5, v___x_3015_);
v___x_3017_ = lean_box(v_types_2983_);
lean_inc_ref(v___f_3016_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3018_, 0, v___x_3017_);
lean_closure_set(v___f_3018_, 1, v_e_2955_);
lean_closure_set(v___f_3018_, 2, v___f_3016_);
if (v_topLevel_2956_ == 0)
{
v___y_2986_ = v___x_3008_;
v___y_2987_ = v___f_3016_;
v___y_2988_ = v___f_3018_;
v___y_2989_ = v___x_2981_;
goto v___jp_2985_;
}
else
{
uint8_t v___x_3019_; 
v___x_3019_ = l_Lean_Expr_isLet(v_e_2955_);
if (v___x_3019_ == 0)
{
uint8_t v___x_3020_; 
v___x_3020_ = l_Lean_Expr_isMData(v_e_2955_);
v___y_2986_ = v___x_3008_;
v___y_2987_ = v___f_3016_;
v___y_2988_ = v___f_3018_;
v___y_2989_ = v___x_3020_;
goto v___jp_2985_;
}
else
{
lean_dec_ref(v___f_3018_);
lean_dec_ref(v_e_2955_);
v___y_2977_ = v___x_3008_;
v___y_2978_ = v___f_3016_;
goto v___jp_2976_;
}
}
}
}
else
{
lean_object* v_val_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref_known(v___x_3008_, 2);
lean_dec_ref(v_e_2955_);
lean_dec(v_fvars_2954_);
v_val_3021_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3010_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_val_3021_);
lean_dec(v___x_3010_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set_tag(v___x_3023_, 0);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_val_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v___x_3029_; 
lean_dec(v_fvars_2954_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_e_2955_);
return v___x_3029_;
}
}
v___jp_3030_:
{
if (v_topLevel_2956_ == 0)
{
lean_object* v___x_3031_; 
lean_dec(v_fvars_2954_);
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_e_2955_);
return v___x_3031_;
}
else
{
v___y_3006_ = v___x_2981_;
goto v___jp_3005_;
}
}
}
else
{
lean_object* v___x_3032_; 
lean_dec(v_fvars_2954_);
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_e_2955_);
return v___x_3032_;
}
v___jp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2968_ = lean_st_ref_take(v_a_2958_);
lean_inc_ref(v_a_2967_);
v___x_2969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_2968_, v___y_2966_, v_a_2967_);
v___x_2970_ = lean_st_ref_put(v_a_2958_, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_a_2967_);
return v___x_2971_;
}
v___jp_2972_:
{
if (lean_obj_tag(v___y_2974_) == 0)
{
lean_object* v_a_2975_; 
v_a_2975_ = lean_ctor_get(v___y_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___y_2974_, 1);
v___y_2966_ = v___y_2973_;
v_a_2967_ = v_a_2975_;
goto v___jp_2965_;
}
else
{
lean_dec_ref(v___y_2973_);
return v___y_2974_;
}
}
v___jp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_box(0);
lean_inc(v_a_2963_);
lean_inc_ref(v_a_2962_);
lean_inc(v_a_2961_);
lean_inc_ref(v_a_2960_);
lean_inc(v_a_2959_);
lean_inc(v_a_2958_);
lean_inc_ref(v_a_2957_);
v___x_2980_ = lean_apply_9(v___y_2978_, v___x_2979_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, lean_box(0));
v___y_2973_ = v___y_2977_;
v___y_2974_ = v___x_2980_;
goto v___jp_2972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3033_, lean_object* v_struct_3034_, uint8_t v___y_3035_, lean_object* v_typeName_3036_, lean_object* v_idx_3037_, lean_object* v_e_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___x_3047_; 
lean_inc_ref(v_struct_3034_);
v___x_3047_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3033_, v_struct_3034_, v___y_3035_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3062_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3062_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3062_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
size_t v___x_3052_; size_t v___x_3053_; uint8_t v___x_3054_; 
v___x_3052_ = lean_ptr_addr(v_struct_3034_);
lean_dec_ref(v_struct_3034_);
v___x_3053_ = lean_ptr_addr(v_a_3048_);
v___x_3054_ = lean_usize_dec_eq(v___x_3052_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3057_; 
lean_dec_ref(v_e_3038_);
v___x_3055_ = l_Lean_Expr_proj___override(v_typeName_3036_, v_idx_3037_, v_a_3048_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3055_);
v___x_3057_ = v___x_3050_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
else
{
lean_object* v___x_3060_; 
lean_dec(v_a_3048_);
lean_dec(v_idx_3037_);
lean_dec(v_typeName_3036_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v_e_3038_);
v___x_3060_ = v___x_3050_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_e_3038_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_dec_ref(v_e_3038_);
lean_dec(v_idx_3037_);
lean_dec(v_typeName_3036_);
lean_dec_ref(v_struct_3034_);
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3063_, lean_object* v_sz_3064_, lean_object* v_i_3065_, lean_object* v_bs_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
size_t v_sz_boxed_3075_; size_t v_i_boxed_3076_; lean_object* v_res_3077_; 
v_sz_boxed_3075_ = lean_unbox_usize(v_sz_3064_);
lean_dec(v_sz_3064_);
v_i_boxed_3076_ = lean_unbox_usize(v_i_3065_);
lean_dec(v_i_3065_);
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3063_, v_sz_boxed_3075_, v_i_boxed_3076_, v_bs_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3078_, lean_object* v_fst_3079_, lean_object* v_fvars_3080_, lean_object* v_a_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3078_, v_fst_3079_, v_fvars_3080_, v_a_3081_, v_b_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_fst_3079_);
lean_dec(v_upperBound_3078_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3092_, lean_object* v_e_3093_, lean_object* v_isLet_3094_, lean_object* v_n_3095_, lean_object* v_t_3096_, lean_object* v_v_3097_, lean_object* v_b_3098_, lean_object* v_topLevel_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
uint8_t v_isLet_boxed_3108_; uint8_t v_topLevel_boxed_3109_; lean_object* v_res_3110_; 
v_isLet_boxed_3108_ = lean_unbox(v_isLet_3094_);
v_topLevel_boxed_3109_ = lean_unbox(v_topLevel_3099_);
v_res_3110_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3092_, v_e_3093_, v_isLet_boxed_3108_, v_n_3095_, v_t_3096_, v_v_3097_, v_b_3098_, v_topLevel_boxed_3109_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3111_, lean_object* v_name_3112_, lean_object* v_type_3113_, lean_object* v_val_3114_, lean_object* v_k_3115_, uint8_t v_nondep_3116_, uint8_t v_kind_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3112_, v_type_3113_, v_val_3114_, v_k_3115_, v_nondep_3116_, v_kind_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3127_, lean_object* v_name_3128_, lean_object* v_type_3129_, lean_object* v_val_3130_, lean_object* v_k_3131_, lean_object* v_nondep_3132_, lean_object* v_kind_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v_nondep_boxed_3142_; uint8_t v_kind_boxed_3143_; lean_object* v_res_3144_; 
v_nondep_boxed_3142_ = lean_unbox(v_nondep_3132_);
v_kind_boxed_3143_ = lean_unbox(v_kind_3133_);
v_res_3144_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3127_, v_name_3128_, v_type_3129_, v_val_3130_, v_k_3131_, v_nondep_boxed_3142_, v_kind_boxed_3143_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3145_, lean_object* v_m_3146_, lean_object* v_a_3147_, lean_object* v_b_3148_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3146_, v_a_3147_, v_b_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3150_, lean_object* v_m_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3151_, v_a_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3154_, lean_object* v_m_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3154_, v_m_3155_, v_a_3156_);
lean_dec_ref(v_a_3156_);
lean_dec_ref(v_m_3155_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3158_, lean_object* v_fst_3159_, lean_object* v_fvars_3160_, lean_object* v_inst_3161_, lean_object* v_R_3162_, lean_object* v_a_3163_, lean_object* v_b_3164_, lean_object* v_c_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3158_, v_fst_3159_, v_fvars_3160_, v_a_3163_, v_b_3164_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3175_, lean_object* v_fst_3176_, lean_object* v_fvars_3177_, lean_object* v_inst_3178_, lean_object* v_R_3179_, lean_object* v_a_3180_, lean_object* v_b_3181_, lean_object* v_c_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3175_, v_fst_3176_, v_fvars_3177_, v_inst_3178_, v_R_3179_, v_a_3180_, v_b_3181_, v_c_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec_ref(v_fst_3176_);
lean_dec(v_upperBound_3175_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3192_, lean_object* v_m_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3193_, v_a_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3196_, lean_object* v_m_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3196_, v_m_3197_, v_a_3198_);
lean_dec_ref(v_a_3198_);
lean_dec_ref(v_m_3197_);
return v_res_3199_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3200_, lean_object* v_a_3201_, lean_object* v_x_3202_){
_start:
{
uint8_t v___x_3203_; 
v___x_3203_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3201_, v_x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3204_, lean_object* v_a_3205_, lean_object* v_x_3206_){
_start:
{
uint8_t v_res_3207_; lean_object* v_r_3208_; 
v_res_3207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3204_, v_a_3205_, v_x_3206_);
lean_dec(v_x_3206_);
lean_dec_ref(v_a_3205_);
v_r_3208_ = lean_box(v_res_3207_);
return v_r_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3209_, lean_object* v_data_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3212_, lean_object* v_a_3213_, lean_object* v_b_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3213_, v_b_3214_, v_x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3217_, lean_object* v_a_3218_, lean_object* v_x_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3218_, v_x_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3221_, lean_object* v_a_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3221_, v_a_3222_, v_x_3223_);
lean_dec(v_x_3223_);
lean_dec_ref(v_a_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3225_, lean_object* v_a_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3226_, v_x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3229_, lean_object* v_a_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3229_, v_a_3230_, v_x_3231_);
lean_dec(v_x_3231_);
lean_dec_ref(v_a_3230_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3233_, lean_object* v_i_3234_, lean_object* v_source_3235_, lean_object* v_target_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3234_, v_source_3235_, v_target_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3238_, lean_object* v_x_3239_, lean_object* v_x_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3239_, v_x_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v___x_3251_; lean_object* v_a_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; 
v___x_3251_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3242_, v_a_3247_);
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3251_);
v___x_3253_ = lean_box(0);
v___x_3254_ = 1;
v___x_3255_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3253_, v_a_3252_, v___x_3254_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3266_, size_t v_i_3267_, lean_object* v_bs_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_usize_dec_lt(v_i_3267_, v_sz_3266_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v_bs_3268_);
return v___x_3278_;
}
else
{
lean_object* v_v_3279_; lean_object* v___x_3280_; lean_object* v_bs_x27_3281_; lean_object* v___x_3282_; 
v_v_3279_ = lean_array_uget(v_bs_3268_, v_i_3267_);
v___x_3280_ = lean_unsigned_to_nat(0u);
v_bs_x27_3281_ = lean_array_uset(v_bs_3268_, v_i_3267_, v___x_3280_);
v___x_3282_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3279_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; size_t v___x_3284_; size_t v___x_3285_; lean_object* v___x_3286_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
v___x_3284_ = ((size_t)1ULL);
v___x_3285_ = lean_usize_add(v_i_3267_, v___x_3284_);
v___x_3286_ = lean_array_uset(v_bs_x27_3281_, v_i_3267_, v_a_3283_);
v_i_3267_ = v___x_3285_;
v_bs_3268_ = v___x_3286_;
goto _start;
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v_bs_x27_3281_);
v_a_3288_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3282_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3282_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3296_, lean_object* v_i_3297_, lean_object* v_bs_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
size_t v_sz_boxed_3307_; size_t v_i_boxed_3308_; lean_object* v_res_3309_; 
v_sz_boxed_3307_ = lean_unbox_usize(v_sz_3296_);
lean_dec(v_sz_3296_);
v_i_boxed_3308_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_res_3309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3307_, v_i_boxed_3308_, v_bs_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; uint8_t v_merge_3330_; 
v_merge_3330_ = lean_ctor_get_uint8(v_a_3311_, 6);
if (v_merge_3330_ == 0)
{
v___y_3320_ = v_a_3311_;
v___y_3321_ = v_a_3312_;
v___y_3322_ = v_a_3313_;
v___y_3323_ = v_a_3314_;
v___y_3324_ = v_a_3315_;
v___y_3325_ = v_a_3316_;
v___y_3326_ = v_a_3317_;
goto v___jp_3319_;
}
else
{
uint8_t v_useContext_3331_; 
v_useContext_3331_ = lean_ctor_get_uint8(v_a_3311_, 7);
if (v_useContext_3331_ == 0)
{
v___y_3320_ = v_a_3311_;
v___y_3321_ = v_a_3312_;
v___y_3322_ = v_a_3313_;
v___y_3323_ = v_a_3314_;
v___y_3324_ = v_a_3315_;
v___y_3325_ = v_a_3316_;
v___y_3326_ = v_a_3317_;
goto v___jp_3319_;
}
else
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_dec_ref_known(v___x_3332_, 1);
v___y_3320_ = v_a_3311_;
v___y_3321_ = v_a_3312_;
v___y_3322_ = v_a_3313_;
v___y_3323_ = v_a_3314_;
v___y_3324_ = v_a_3315_;
v___y_3325_ = v_a_3316_;
v___y_3326_ = v_a_3317_;
goto v___jp_3319_;
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref(v_es_3310_);
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
v___jp_3319_:
{
size_t v_sz_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
v_sz_3327_ = lean_array_size(v_es_3310_);
v___x_3328_ = ((size_t)0ULL);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3327_, v___x_3328_, v_es_3310_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Meta_ExtractLets_extract(v_es_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3351_, lean_object* v_x_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3351_, v_x_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3358_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3358_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3358_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3375_, lean_object* v_x_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3375_, v_x_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3383_, lean_object* v_decls_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3384_, v_x_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3392_, lean_object* v_decls_3393_, lean_object* v_x_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3392_, v_decls_3393_, v_x_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3401_, size_t v_i_3402_, lean_object* v_bs_3403_){
_start:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_usize_dec_lt(v_i_3402_, v_sz_3401_);
if (v___x_3404_ == 0)
{
return v_bs_3403_;
}
else
{
lean_object* v_v_3405_; lean_object* v___x_3406_; lean_object* v_bs_x27_3407_; lean_object* v___x_3408_; size_t v___x_3409_; size_t v___x_3410_; lean_object* v___x_3411_; 
v_v_3405_ = lean_array_uget(v_bs_3403_, v_i_3402_);
v___x_3406_ = lean_unsigned_to_nat(0u);
v_bs_x27_3407_ = lean_array_uset(v_bs_3403_, v_i_3402_, v___x_3406_);
v___x_3408_ = l_Lean_LocalDecl_fvarId(v_v_3405_);
lean_dec(v_v_3405_);
v___x_3409_ = ((size_t)1ULL);
v___x_3410_ = lean_usize_add(v_i_3402_, v___x_3409_);
v___x_3411_ = lean_array_uset(v_bs_x27_3407_, v_i_3402_, v___x_3408_);
v_i_3402_ = v___x_3410_;
v_bs_3403_ = v___x_3411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3413_, lean_object* v_i_3414_, lean_object* v_bs_3415_){
_start:
{
size_t v_sz_boxed_3416_; size_t v_i_boxed_3417_; lean_object* v_res_3418_; 
v_sz_boxed_3416_ = lean_unbox_usize(v_sz_3413_);
lean_dec(v_sz_3413_);
v_i_boxed_3417_ = lean_unbox_usize(v_i_3414_);
lean_dec(v_i_3414_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3416_, v_i_boxed_3417_, v_bs_3415_);
return v_res_3418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_unsigned_to_nat(16u);
v___x_3421_ = lean_mk_array(v___x_3420_, v___x_3419_);
return v___x_3421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
lean_ctor_set(v___x_3424_, 1, v___x_3422_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3425_, lean_object* v_givenNames_3426_, lean_object* v_k_3427_, lean_object* v_config_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3435_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3436_, 0, v_givenNames_3426_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
lean_ctor_set(v___x_3436_, 2, v___x_3434_);
v___x_3437_ = lean_st_mk_ref(v___x_3436_);
v___x_3438_ = lean_st_mk_ref(v___x_3434_);
v___x_3439_ = l_Lean_Meta_ExtractLets_extract(v_es_3425_, v_config_3428_, v___x_3438_, v___x_3437_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v_givenNames_3443_; lean_object* v_decls_3444_; size_t v_sz_3445_; size_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; size_t v_sz_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = lean_st_ref_get(v___x_3438_);
lean_dec(v___x_3438_);
lean_dec(v___x_3441_);
v___x_3442_ = lean_st_ref_get(v___x_3437_);
lean_dec(v___x_3437_);
v_givenNames_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_givenNames_3443_);
v_decls_3444_ = lean_ctor_get(v___x_3442_, 1);
lean_inc_ref(v_decls_3444_);
lean_dec(v___x_3442_);
v_sz_3445_ = lean_array_size(v_decls_3444_);
v___x_3446_ = ((size_t)0ULL);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_3445_, v___x_3446_, v_decls_3444_);
lean_inc_ref(v___x_3447_);
v___x_3448_ = lean_array_to_list(v___x_3447_);
v_sz_3449_ = lean_array_size(v___x_3447_);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3449_, v___x_3446_, v___x_3447_);
v___x_3451_ = lean_apply_3(v_k_3427_, v___x_3450_, v_a_3440_, v_givenNames_3443_);
v___x_3452_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3448_, v___x_3451_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_);
return v___x_3452_;
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v___x_3438_);
lean_dec(v___x_3437_);
lean_dec_ref(v_k_3427_);
v_a_3453_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3439_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3439_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3461_, lean_object* v_givenNames_3462_, lean_object* v_k_3463_, lean_object* v_config_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3461_, v_givenNames_3462_, v_k_3463_, v_config_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec_ref(v_config_3464_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3471_, lean_object* v_es_3472_, lean_object* v_givenNames_3473_, lean_object* v_k_3474_, lean_object* v_config_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v___x_3481_; 
v___x_3481_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3472_, v_givenNames_3473_, v_k_3474_, v_config_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3482_, lean_object* v_es_3483_, lean_object* v_givenNames_3484_, lean_object* v_k_3485_, lean_object* v_config_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3482_, v_es_3483_, v_givenNames_3484_, v_k_3485_, v_config_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec_ref(v_config_3486_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3493_, lean_object* v_runInBase_3494_, lean_object* v_b_3495_, lean_object* v_c_3496_, lean_object* v_d_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_apply_3(v_k_3493_, v_b_3495_, v_c_3496_, v_d_3497_);
lean_inc(v___y_3501_);
lean_inc_ref(v___y_3500_);
lean_inc(v___y_3499_);
lean_inc_ref(v___y_3498_);
v___x_3504_ = lean_apply_7(v_runInBase_3494_, lean_box(0), v___x_3503_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, lean_box(0));
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3505_, lean_object* v_runInBase_3506_, lean_object* v_b_3507_, lean_object* v_c_3508_, lean_object* v_d_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3505_, v_runInBase_3506_, v_b_3507_, v_c_3508_, v_d_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3516_, lean_object* v_es_3517_, lean_object* v_givenNames_3518_, lean_object* v_config_3519_, lean_object* v_runInBase_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___f_3526_; lean_object* v___x_3527_; 
v___f_3526_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3526_, 0, v_k_3516_);
lean_closure_set(v___f_3526_, 1, v_runInBase_3520_);
v___x_3527_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3517_, v_givenNames_3518_, v___f_3526_, v_config_3519_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3528_, lean_object* v_es_3529_, lean_object* v_givenNames_3530_, lean_object* v_config_3531_, lean_object* v_runInBase_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3528_, v_es_3529_, v_givenNames_3530_, v_config_3531_, v_runInBase_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v_config_3531_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_es_3541_, lean_object* v_givenNames_3542_, lean_object* v_k_3543_, lean_object* v_config_3544_){
_start:
{
lean_object* v_toBind_3545_; lean_object* v_liftWith_3546_; lean_object* v_restoreM_3547_; lean_object* v___f_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_toBind_3545_ = lean_ctor_get(v_inst_3539_, 1);
lean_inc(v_toBind_3545_);
lean_dec_ref(v_inst_3539_);
v_liftWith_3546_ = lean_ctor_get(v_inst_3540_, 0);
lean_inc(v_liftWith_3546_);
v_restoreM_3547_ = lean_ctor_get(v_inst_3540_, 1);
lean_inc(v_restoreM_3547_);
lean_dec_ref(v_inst_3540_);
v___f_3548_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3548_, 0, v_k_3543_);
lean_closure_set(v___f_3548_, 1, v_es_3541_);
lean_closure_set(v___f_3548_, 2, v_givenNames_3542_);
lean_closure_set(v___f_3548_, 3, v_config_3544_);
v___x_3549_ = lean_apply_2(v_liftWith_3546_, lean_box(0), v___f_3548_);
v___x_3550_ = lean_apply_1(v_restoreM_3547_, lean_box(0));
v___x_3551_ = lean_apply_4(v_toBind_3545_, lean_box(0), lean_box(0), v___x_3549_, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3552_, lean_object* v_00_u03b1_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_es_3556_, lean_object* v_givenNames_3557_, lean_object* v_k_3558_, lean_object* v_config_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_Meta_extractLets___redArg(v_inst_3554_, v_inst_3555_, v_es_3556_, v_givenNames_3557_, v_k_3558_, v_config_3559_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3562_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3563_ = lean_box(0);
v___x_3564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3562_);
lean_ctor_set(v___x_3564_, 2, v___x_3561_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3565_, lean_object* v_config_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
uint8_t v_proofs_3572_; uint8_t v_types_3573_; uint8_t v_implicits_3574_; uint8_t v_descend_3575_; uint8_t v_underBinder_3576_; uint8_t v_usedOnly_3577_; uint8_t v_merge_3578_; uint8_t v_useContext_3579_; uint8_t v_preserveBinderNames_3580_; uint8_t v_lift_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3620_; 
v_proofs_3572_ = lean_ctor_get_uint8(v_config_3566_, 0);
v_types_3573_ = lean_ctor_get_uint8(v_config_3566_, 1);
v_implicits_3574_ = lean_ctor_get_uint8(v_config_3566_, 2);
v_descend_3575_ = lean_ctor_get_uint8(v_config_3566_, 3);
v_underBinder_3576_ = lean_ctor_get_uint8(v_config_3566_, 4);
v_usedOnly_3577_ = lean_ctor_get_uint8(v_config_3566_, 5);
v_merge_3578_ = lean_ctor_get_uint8(v_config_3566_, 6);
v_useContext_3579_ = lean_ctor_get_uint8(v_config_3566_, 7);
v_preserveBinderNames_3580_ = lean_ctor_get_uint8(v_config_3566_, 9);
v_lift_3581_ = lean_ctor_get_uint8(v_config_3566_, 10);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_config_3566_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3583_ = v_config_3566_;
v_isShared_3584_ = v_isSharedCheck_3620_;
goto v_resetjp_3582_;
}
else
{
lean_dec(v_config_3566_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3620_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; lean_object* v___x_3591_; 
v___x_3585_ = l_Lean_instInhabitedExpr;
v___x_3586_ = lean_unsigned_to_nat(1u);
v___x_3587_ = lean_mk_empty_array_with_capacity(v___x_3586_);
v___x_3588_ = lean_array_push(v___x_3587_, v_e_3565_);
v___x_3589_ = 1;
if (v_isShared_3584_ == 0)
{
v___x_3591_ = v___x_3583_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 0, v_proofs_3572_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 1, v_types_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 2, v_implicits_3574_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 3, v_descend_3575_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 4, v_underBinder_3576_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 5, v_usedOnly_3577_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 6, v_merge_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 7, v_useContext_3579_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 9, v_preserveBinderNames_3580_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, 10, v_lift_3581_);
v___x_3591_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_ctor_set_uint8(v___x_3591_, 8, v___x_3589_);
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3594_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3595_ = lean_st_mk_ref(v___x_3594_);
v___x_3596_ = lean_st_mk_ref(v___x_3593_);
v___x_3597_ = l_Lean_Meta_ExtractLets_extract(v___x_3588_, v___x_3591_, v___x_3596_, v___x_3595_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
lean_dec_ref(v___x_3591_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3610_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3610_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3610_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v_decls_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3602_ = lean_st_ref_get(v___x_3596_);
lean_dec(v___x_3596_);
lean_dec(v___x_3602_);
v___x_3603_ = lean_st_ref_get(v___x_3595_);
lean_dec(v___x_3595_);
v_decls_3604_ = lean_ctor_get(v___x_3603_, 1);
lean_inc_ref(v_decls_3604_);
lean_dec(v___x_3603_);
v___x_3605_ = lean_array_get(v___x_3585_, v_a_3598_, v___x_3592_);
lean_dec(v_a_3598_);
v___x_3606_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3604_, v___x_3605_);
lean_dec_ref(v_decls_3604_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3606_);
v___x_3608_ = v___x_3600_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v___x_3596_);
lean_dec(v___x_3595_);
v_a_3611_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3597_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3597_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3621_, lean_object* v_config_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Meta_liftLets(v_e_3621_, v_config_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
return v_res_3628_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3631_ = l_Lean_stringToMessageData(v___x_3630_);
return v___x_3631_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3634_, lean_object* v_mvarId_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3642_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3634_, v_mvarId_3635_, v___x_3641_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3643_, lean_object* v_mvarId_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3643_, v_mvarId_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
lean_dec(v_a_3648_);
lean_dec_ref(v_a_3647_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3651_, lean_object* v_tactic_3652_, lean_object* v_mvarId_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3652_, v_mvarId_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3660_, lean_object* v_tactic_3661_, lean_object* v_mvarId_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3660_, v_tactic_3661_, v_mvarId_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
lean_dec(v_a_3666_);
lean_dec_ref(v_a_3665_);
lean_dec(v_a_3664_);
lean_dec_ref(v_a_3663_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3669_, lean_object* v_b_3670_, lean_object* v_c_3671_, lean_object* v_d_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___x_3678_; 
lean_inc(v___y_3676_);
lean_inc_ref(v___y_3675_);
lean_inc(v___y_3674_);
lean_inc_ref(v___y_3673_);
v___x_3678_ = lean_apply_8(v_k_3669_, v_b_3670_, v_c_3671_, v_d_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, lean_box(0));
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3679_, lean_object* v_b_3680_, lean_object* v_c_3681_, lean_object* v_d_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3679_, v_b_3680_, v_c_3681_, v_d_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3689_, lean_object* v_givenNames_3690_, lean_object* v_k_3691_, lean_object* v_config_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___f_3698_; lean_object* v___x_3699_; 
v___f_3698_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3698_, 0, v_k_3691_);
v___x_3699_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3689_, v_givenNames_3690_, v___f_3698_, v_config_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
v_a_3708_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3699_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3699_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3716_, lean_object* v_givenNames_3717_, lean_object* v_k_3718_, lean_object* v_config_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3716_, v_givenNames_3717_, v_k_3718_, v_config_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v_config_3719_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3726_, lean_object* v_es_3727_, lean_object* v_givenNames_3728_, lean_object* v_k_3729_, lean_object* v_config_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3727_, v_givenNames_3728_, v_k_3729_, v_config_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3737_, lean_object* v_es_3738_, lean_object* v_givenNames_3739_, lean_object* v_k_3740_, lean_object* v_config_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3737_, v_es_3738_, v_givenNames_3739_, v_k_3740_, v_config_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec_ref(v_config_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3748_, lean_object* v_x_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3748_, v_x_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
v_a_3764_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3755_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3755_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3772_, lean_object* v_x_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3772_, v_x_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3780_, lean_object* v_mvarId_3781_, lean_object* v_x_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3781_, v_x_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3789_, lean_object* v_mvarId_3790_, lean_object* v_x_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3789_, v_mvarId_3790_, v_x_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3798_, lean_object* v_x_3799_, lean_object* v_x_3800_, lean_object* v_x_3801_){
_start:
{
lean_object* v_ks_3802_; lean_object* v_vs_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3827_; 
v_ks_3802_ = lean_ctor_get(v_x_3798_, 0);
v_vs_3803_ = lean_ctor_get(v_x_3798_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_x_3798_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3805_ = v_x_3798_;
v_isShared_3806_ = v_isSharedCheck_3827_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_vs_3803_);
lean_inc(v_ks_3802_);
lean_dec(v_x_3798_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3827_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3807_ = lean_array_get_size(v_ks_3802_);
v___x_3808_ = lean_nat_dec_lt(v_x_3799_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
lean_dec(v_x_3799_);
v___x_3809_ = lean_array_push(v_ks_3802_, v_x_3800_);
v___x_3810_ = lean_array_push(v_vs_3803_, v_x_3801_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v___x_3810_);
lean_ctor_set(v___x_3805_, 0, v___x_3809_);
v___x_3812_ = v___x_3805_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
else
{
lean_object* v_k_x27_3814_; uint8_t v___x_3815_; 
v_k_x27_3814_ = lean_array_fget_borrowed(v_ks_3802_, v_x_3799_);
v___x_3815_ = l_Lean_instBEqMVarId_beq(v_x_3800_, v_k_x27_3814_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3817_; 
if (v_isShared_3806_ == 0)
{
v___x_3817_ = v___x_3805_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_ks_3802_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_vs_3803_);
v___x_3817_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = lean_unsigned_to_nat(1u);
v___x_3819_ = lean_nat_add(v_x_3799_, v___x_3818_);
lean_dec(v_x_3799_);
v_x_3798_ = v___x_3817_;
v_x_3799_ = v___x_3819_;
goto _start;
}
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3822_ = lean_array_fset(v_ks_3802_, v_x_3799_, v_x_3800_);
v___x_3823_ = lean_array_fset(v_vs_3803_, v_x_3799_, v_x_3801_);
lean_dec(v_x_3799_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 1, v___x_3823_);
lean_ctor_set(v___x_3805_, 0, v___x_3822_);
v___x_3825_ = v___x_3805_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3828_, lean_object* v_k_3829_, lean_object* v_v_3830_){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_unsigned_to_nat(0u);
v___x_3832_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3828_, v___x_3831_, v_k_3829_, v_v_3830_);
return v___x_3832_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3834_, size_t v_x_3835_, size_t v_x_3836_, lean_object* v_x_3837_, lean_object* v_x_3838_){
_start:
{
if (lean_obj_tag(v_x_3834_) == 0)
{
lean_object* v_es_3839_; size_t v___x_3840_; size_t v___x_3841_; lean_object* v_j_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v_es_3839_ = lean_ctor_get(v_x_3834_, 0);
v___x_3840_ = ((size_t)31ULL);
v___x_3841_ = lean_usize_land(v_x_3835_, v___x_3840_);
v_j_3842_ = lean_usize_to_nat(v___x_3841_);
v___x_3843_ = lean_array_get_size(v_es_3839_);
v___x_3844_ = lean_nat_dec_lt(v_j_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
lean_dec(v_j_3842_);
lean_dec(v_x_3838_);
lean_dec(v_x_3837_);
return v_x_3834_;
}
else
{
lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3883_; 
lean_inc_ref(v_es_3839_);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_x_3834_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; 
v_unused_3884_ = lean_ctor_get(v_x_3834_, 0);
lean_dec(v_unused_3884_);
v___x_3846_ = v_x_3834_;
v_isShared_3847_ = v_isSharedCheck_3883_;
goto v_resetjp_3845_;
}
else
{
lean_dec(v_x_3834_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3883_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v_v_3848_; lean_object* v___x_3849_; lean_object* v_xs_x27_3850_; lean_object* v___y_3852_; 
v_v_3848_ = lean_array_fget(v_es_3839_, v_j_3842_);
v___x_3849_ = lean_box(0);
v_xs_x27_3850_ = lean_array_fset(v_es_3839_, v_j_3842_, v___x_3849_);
switch(lean_obj_tag(v_v_3848_))
{
case 0:
{
lean_object* v_key_3857_; lean_object* v_val_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3868_; 
v_key_3857_ = lean_ctor_get(v_v_3848_, 0);
v_val_3858_ = lean_ctor_get(v_v_3848_, 1);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_v_3848_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3860_ = v_v_3848_;
v_isShared_3861_ = v_isSharedCheck_3868_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_val_3858_);
lean_inc(v_key_3857_);
lean_dec(v_v_3848_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3868_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
uint8_t v___x_3862_; 
v___x_3862_ = l_Lean_instBEqMVarId_beq(v_x_3837_, v_key_3857_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_del_object(v___x_3860_);
v___x_3863_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3857_, v_val_3858_, v_x_3837_, v_x_3838_);
v___x_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
v___y_3852_ = v___x_3864_;
goto v___jp_3851_;
}
else
{
lean_object* v___x_3866_; 
lean_dec(v_val_3858_);
lean_dec(v_key_3857_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 1, v_x_3838_);
lean_ctor_set(v___x_3860_, 0, v_x_3837_);
v___x_3866_ = v___x_3860_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_x_3837_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_x_3838_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
v___y_3852_ = v___x_3866_;
goto v___jp_3851_;
}
}
}
}
case 1:
{
lean_object* v_node_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3881_; 
v_node_3869_ = lean_ctor_get(v_v_3848_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_v_3848_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3871_ = v_v_3848_;
v_isShared_3872_ = v_isSharedCheck_3881_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_node_3869_);
lean_dec(v_v_3848_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3881_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
size_t v___x_3873_; size_t v___x_3874_; size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3873_ = ((size_t)5ULL);
v___x_3874_ = lean_usize_shift_right(v_x_3835_, v___x_3873_);
v___x_3875_ = ((size_t)1ULL);
v___x_3876_ = lean_usize_add(v_x_3836_, v___x_3875_);
v___x_3877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3869_, v___x_3874_, v___x_3876_, v_x_3837_, v_x_3838_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v___x_3877_);
v___x_3879_ = v___x_3871_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
v___y_3852_ = v___x_3879_;
goto v___jp_3851_;
}
}
}
default: 
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v_x_3837_);
lean_ctor_set(v___x_3882_, 1, v_x_3838_);
v___y_3852_ = v___x_3882_;
goto v___jp_3851_;
}
}
v___jp_3851_:
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
v___x_3853_ = lean_array_fset(v_xs_x27_3850_, v_j_3842_, v___y_3852_);
lean_dec(v_j_3842_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3853_);
v___x_3855_ = v___x_3846_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
else
{
lean_object* v_ks_3885_; lean_object* v_vs_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3904_; 
v_ks_3885_ = lean_ctor_get(v_x_3834_, 0);
v_vs_3886_ = lean_ctor_get(v_x_3834_, 1);
v_isSharedCheck_3904_ = !lean_is_exclusive(v_x_3834_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3888_ = v_x_3834_;
v_isShared_3889_ = v_isSharedCheck_3904_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_vs_3886_);
lean_inc(v_ks_3885_);
lean_dec(v_x_3834_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3904_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_ks_3885_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_vs_3886_);
v___x_3891_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v_newNode_3892_; size_t v___x_3893_; uint8_t v___x_3894_; 
v_newNode_3892_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3891_, v_x_3837_, v_x_3838_);
v___x_3893_ = ((size_t)7ULL);
v___x_3894_ = lean_usize_dec_le(v___x_3893_, v_x_3836_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3895_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3892_);
v___x_3896_ = lean_unsigned_to_nat(4u);
v___x_3897_ = lean_nat_dec_lt(v___x_3895_, v___x_3896_);
lean_dec(v___x_3895_);
if (v___x_3897_ == 0)
{
lean_object* v_ks_3898_; lean_object* v_vs_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_ks_3898_ = lean_ctor_get(v_newNode_3892_, 0);
lean_inc_ref(v_ks_3898_);
v_vs_3899_ = lean_ctor_get(v_newNode_3892_, 1);
lean_inc_ref(v_vs_3899_);
lean_dec_ref(v_newNode_3892_);
v___x_3900_ = lean_unsigned_to_nat(0u);
v___x_3901_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3836_, v_ks_3898_, v_vs_3899_, v___x_3900_, v___x_3901_);
lean_dec_ref(v_vs_3899_);
lean_dec_ref(v_ks_3898_);
return v___x_3902_;
}
else
{
return v_newNode_3892_;
}
}
else
{
return v_newNode_3892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3905_, lean_object* v_keys_3906_, lean_object* v_vals_3907_, lean_object* v_i_3908_, lean_object* v_entries_3909_){
_start:
{
lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = lean_array_get_size(v_keys_3906_);
v___x_3911_ = lean_nat_dec_lt(v_i_3908_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_dec(v_i_3908_);
return v_entries_3909_;
}
else
{
lean_object* v_k_3912_; lean_object* v_v_3913_; uint64_t v___x_3914_; size_t v_h_3915_; size_t v___x_3916_; lean_object* v___x_3917_; size_t v___x_3918_; size_t v___x_3919_; size_t v___x_3920_; size_t v_h_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_k_3912_ = lean_array_fget_borrowed(v_keys_3906_, v_i_3908_);
v_v_3913_ = lean_array_fget_borrowed(v_vals_3907_, v_i_3908_);
v___x_3914_ = l_Lean_instHashableMVarId_hash(v_k_3912_);
v_h_3915_ = lean_uint64_to_usize(v___x_3914_);
v___x_3916_ = ((size_t)5ULL);
v___x_3917_ = lean_unsigned_to_nat(1u);
v___x_3918_ = ((size_t)1ULL);
v___x_3919_ = lean_usize_sub(v_depth_3905_, v___x_3918_);
v___x_3920_ = lean_usize_mul(v___x_3916_, v___x_3919_);
v_h_3921_ = lean_usize_shift_right(v_h_3915_, v___x_3920_);
v___x_3922_ = lean_nat_add(v_i_3908_, v___x_3917_);
lean_dec(v_i_3908_);
lean_inc(v_v_3913_);
lean_inc(v_k_3912_);
v___x_3923_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3909_, v_h_3921_, v_depth_3905_, v_k_3912_, v_v_3913_);
v_i_3908_ = v___x_3922_;
v_entries_3909_ = v___x_3923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3925_, lean_object* v_keys_3926_, lean_object* v_vals_3927_, lean_object* v_i_3928_, lean_object* v_entries_3929_){
_start:
{
size_t v_depth_boxed_3930_; lean_object* v_res_3931_; 
v_depth_boxed_3930_ = lean_unbox_usize(v_depth_3925_);
lean_dec(v_depth_3925_);
v_res_3931_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3930_, v_keys_3926_, v_vals_3927_, v_i_3928_, v_entries_3929_);
lean_dec_ref(v_vals_3927_);
lean_dec_ref(v_keys_3926_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3932_, lean_object* v_x_3933_, lean_object* v_x_3934_, lean_object* v_x_3935_, lean_object* v_x_3936_){
_start:
{
size_t v_x_2298__boxed_3937_; size_t v_x_2299__boxed_3938_; lean_object* v_res_3939_; 
v_x_2298__boxed_3937_ = lean_unbox_usize(v_x_3933_);
lean_dec(v_x_3933_);
v_x_2299__boxed_3938_ = lean_unbox_usize(v_x_3934_);
lean_dec(v_x_3934_);
v_res_3939_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3932_, v_x_2298__boxed_3937_, v_x_2299__boxed_3938_, v_x_3935_, v_x_3936_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3940_, lean_object* v_x_3941_, lean_object* v_x_3942_){
_start:
{
uint64_t v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; lean_object* v___x_3946_; 
v___x_3943_ = l_Lean_instHashableMVarId_hash(v_x_3941_);
v___x_3944_ = lean_uint64_to_usize(v___x_3943_);
v___x_3945_ = ((size_t)1ULL);
v___x_3946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3940_, v___x_3944_, v___x_3945_, v_x_3941_, v_x_3942_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_3947_, lean_object* v_val_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v___x_3951_; lean_object* v_mctx_3952_; lean_object* v_cache_3953_; lean_object* v_zetaDeltaFVarIds_3954_; lean_object* v_postponed_3955_; lean_object* v_diag_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3985_; 
v___x_3951_ = lean_st_ref_take(v___y_3949_);
v_mctx_3952_ = lean_ctor_get(v___x_3951_, 0);
v_cache_3953_ = lean_ctor_get(v___x_3951_, 1);
v_zetaDeltaFVarIds_3954_ = lean_ctor_get(v___x_3951_, 2);
v_postponed_3955_ = lean_ctor_get(v___x_3951_, 3);
v_diag_3956_ = lean_ctor_get(v___x_3951_, 4);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3958_ = v___x_3951_;
v_isShared_3959_ = v_isSharedCheck_3985_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_diag_3956_);
lean_inc(v_postponed_3955_);
lean_inc(v_zetaDeltaFVarIds_3954_);
lean_inc(v_cache_3953_);
lean_inc(v_mctx_3952_);
lean_dec(v___x_3951_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3985_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v_depth_3960_; lean_object* v_levelAssignDepth_3961_; lean_object* v_lmvarCounter_3962_; lean_object* v_mvarCounter_3963_; lean_object* v_lDecls_3964_; lean_object* v_decls_3965_; lean_object* v_userNames_3966_; lean_object* v_lAssignment_3967_; lean_object* v_eAssignment_3968_; lean_object* v_dAssignment_3969_; lean_object* v_instanceTypedMVars_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3984_; 
v_depth_3960_ = lean_ctor_get(v_mctx_3952_, 0);
v_levelAssignDepth_3961_ = lean_ctor_get(v_mctx_3952_, 1);
v_lmvarCounter_3962_ = lean_ctor_get(v_mctx_3952_, 2);
v_mvarCounter_3963_ = lean_ctor_get(v_mctx_3952_, 3);
v_lDecls_3964_ = lean_ctor_get(v_mctx_3952_, 4);
v_decls_3965_ = lean_ctor_get(v_mctx_3952_, 5);
v_userNames_3966_ = lean_ctor_get(v_mctx_3952_, 6);
v_lAssignment_3967_ = lean_ctor_get(v_mctx_3952_, 7);
v_eAssignment_3968_ = lean_ctor_get(v_mctx_3952_, 8);
v_dAssignment_3969_ = lean_ctor_get(v_mctx_3952_, 9);
v_instanceTypedMVars_3970_ = lean_ctor_get(v_mctx_3952_, 10);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_mctx_3952_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3972_ = v_mctx_3952_;
v_isShared_3973_ = v_isSharedCheck_3984_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_instanceTypedMVars_3970_);
lean_inc(v_dAssignment_3969_);
lean_inc(v_eAssignment_3968_);
lean_inc(v_lAssignment_3967_);
lean_inc(v_userNames_3966_);
lean_inc(v_decls_3965_);
lean_inc(v_lDecls_3964_);
lean_inc(v_mvarCounter_3963_);
lean_inc(v_lmvarCounter_3962_);
lean_inc(v_levelAssignDepth_3961_);
lean_inc(v_depth_3960_);
lean_dec(v_mctx_3952_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3984_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3977_; 
v___x_3974_ = lean_box(0);
v___x_3975_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_3968_, v_mvarId_3947_, v_val_3948_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 8, v___x_3975_);
v___x_3977_ = v___x_3972_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_depth_3960_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_levelAssignDepth_3961_);
lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_lmvarCounter_3962_);
lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_mvarCounter_3963_);
lean_ctor_set(v_reuseFailAlloc_3983_, 4, v_lDecls_3964_);
lean_ctor_set(v_reuseFailAlloc_3983_, 5, v_decls_3965_);
lean_ctor_set(v_reuseFailAlloc_3983_, 6, v_userNames_3966_);
lean_ctor_set(v_reuseFailAlloc_3983_, 7, v_lAssignment_3967_);
lean_ctor_set(v_reuseFailAlloc_3983_, 8, v___x_3975_);
lean_ctor_set(v_reuseFailAlloc_3983_, 9, v_dAssignment_3969_);
lean_ctor_set(v_reuseFailAlloc_3983_, 10, v_instanceTypedMVars_3970_);
v___x_3977_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3979_; 
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3977_);
v___x_3979_ = v___x_3958_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_cache_3953_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_zetaDeltaFVarIds_3954_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_postponed_3955_);
lean_ctor_set(v_reuseFailAlloc_3982_, 4, v_diag_3956_);
v___x_3979_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_st_ref_put(v___y_3949_, v___x_3979_);
v___x_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3974_);
return v___x_3981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_3986_, lean_object* v_val_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_3986_, v_val_3987_, v___y_3988_);
lean_dec(v___y_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_3991_, size_t v_i_3992_, lean_object* v_bs_3993_){
_start:
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_usize_dec_lt(v_i_3992_, v_sz_3991_);
if (v___x_3994_ == 0)
{
return v_bs_3993_;
}
else
{
lean_object* v_v_3995_; lean_object* v___x_3996_; lean_object* v_bs_x27_3997_; lean_object* v___x_3998_; size_t v___x_3999_; size_t v___x_4000_; lean_object* v___x_4001_; 
v_v_3995_ = lean_array_uget(v_bs_3993_, v_i_3992_);
v___x_3996_ = lean_unsigned_to_nat(0u);
v_bs_x27_3997_ = lean_array_uset(v_bs_3993_, v_i_3992_, v___x_3996_);
v___x_3998_ = l_Lean_Expr_fvar___override(v_v_3995_);
v___x_3999_ = ((size_t)1ULL);
v___x_4000_ = lean_usize_add(v_i_3992_, v___x_3999_);
v___x_4001_ = lean_array_uset(v_bs_x27_3997_, v_i_3992_, v___x_3998_);
v_i_3992_ = v___x_4000_;
v_bs_3993_ = v___x_4001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4003_, lean_object* v_i_4004_, lean_object* v_bs_4005_){
_start:
{
size_t v_sz_boxed_4006_; size_t v_i_boxed_4007_; lean_object* v_res_4008_; 
v_sz_boxed_4006_ = lean_unbox_usize(v_sz_4003_);
lean_dec(v_sz_4003_);
v_i_boxed_4007_ = lean_unbox_usize(v_i_4004_);
lean_dec(v_i_4004_);
v_res_4008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4006_, v_i_boxed_4007_, v_bs_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4009_, lean_object* v_mvarId_4010_, lean_object* v_a_4011_, lean_object* v___x_4012_, lean_object* v_fvarIds_4013_, lean_object* v_es_4014_, lean_object* v_givenNames_x27_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4072_; uint8_t v___x_4073_; 
v___x_4021_ = lean_unsigned_to_nat(0u);
v___x_4022_ = lean_array_get_borrowed(v___x_4009_, v_es_4014_, v___x_4021_);
v___x_4072_ = lean_array_get_size(v_fvarIds_4013_);
v___x_4073_ = lean_nat_dec_eq(v___x_4072_, v___x_4021_);
if (v___x_4073_ == 0)
{
lean_dec(v___x_4012_);
goto v___jp_4023_;
}
else
{
uint8_t v___x_4074_; 
v___x_4074_ = lean_expr_eqv(v_a_4011_, v___x_4022_);
if (v___x_4074_ == 0)
{
lean_dec(v___x_4012_);
goto v___jp_4023_;
}
else
{
lean_object* v___x_4075_; 
lean_inc(v_mvarId_4010_);
v___x_4075_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4012_, v_mvarId_4010_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_dec_ref_known(v___x_4075_, 1);
goto v___jp_4023_;
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec(v_givenNames_x27_4015_);
lean_dec_ref(v_fvarIds_4013_);
lean_dec(v_mvarId_4010_);
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
}
v___jp_4023_:
{
lean_object* v___x_4024_; 
lean_inc(v_mvarId_4010_);
v___x_4024_ = l_Lean_MVarId_getTag(v_mvarId_4010_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4026_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
lean_inc(v___x_4022_);
v___x_4026_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4022_, v_a_4025_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; size_t v_sz_4028_; size_t v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; uint8_t v___x_4032_; uint8_t v___x_4033_; lean_object* v___x_4034_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_n(v_a_4027_, 2);
lean_dec_ref_known(v___x_4026_, 1);
v_sz_4028_ = lean_array_size(v_fvarIds_4013_);
v___x_4029_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4013_);
v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4028_, v___x_4029_, v_fvarIds_4013_);
v___x_4031_ = 0;
v___x_4032_ = 1;
v___x_4033_ = 1;
v___x_4034_ = l_Lean_Meta_mkLetFVars(v___x_4030_, v_a_4027_, v___x_4031_, v___x_4032_, v___x_4033_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec_ref(v___x_4030_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4046_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v___x_4036_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4010_, v_a_4035_, v___y_4017_);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4046_ == 0)
{
lean_object* v_unused_4047_; 
v_unused_4047_ = lean_ctor_get(v___x_4036_, 0);
lean_dec(v_unused_4047_);
v___x_4038_ = v___x_4036_;
v_isShared_4039_ = v_isSharedCheck_4046_;
goto v_resetjp_4037_;
}
else
{
lean_dec(v___x_4036_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4046_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
v___x_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4040_, 0, v_fvarIds_4013_);
lean_ctor_set(v___x_4040_, 1, v_givenNames_x27_4015_);
v___x_4041_ = l_Lean_Expr_mvarId_x21(v_a_4027_);
lean_dec(v_a_4027_);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4042_);
v___x_4044_ = v___x_4038_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v_a_4027_);
lean_dec(v_givenNames_x27_4015_);
lean_dec_ref(v_fvarIds_4013_);
lean_dec(v_mvarId_4010_);
v_a_4048_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4034_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4034_);
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
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_givenNames_x27_4015_);
lean_dec_ref(v_fvarIds_4013_);
lean_dec(v_mvarId_4010_);
v_a_4056_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4026_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4026_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_givenNames_x27_4015_);
lean_dec_ref(v_fvarIds_4013_);
lean_dec(v_mvarId_4010_);
v_a_4064_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4024_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4024_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4084_, lean_object* v_mvarId_4085_, lean_object* v_a_4086_, lean_object* v___x_4087_, lean_object* v_fvarIds_4088_, lean_object* v_es_4089_, lean_object* v_givenNames_x27_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_MVarId_extractLets___lam__0(v___x_4084_, v_mvarId_4085_, v_a_4086_, v___x_4087_, v_fvarIds_4088_, v_es_4089_, v_givenNames_x27_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec_ref(v_es_4089_);
lean_dec_ref(v_a_4086_);
lean_dec_ref(v___x_4084_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4097_, lean_object* v___x_4098_, lean_object* v___x_4099_, lean_object* v_givenNames_4100_, lean_object* v_config_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v___x_4107_; 
lean_inc(v___x_4098_);
lean_inc(v_mvarId_4097_);
v___x_4107_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4097_, v___x_4098_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v___x_4108_; 
lean_dec_ref_known(v___x_4107_, 1);
lean_inc(v_mvarId_4097_);
v___x_4108_ = l_Lean_MVarId_getType(v_mvarId_4097_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___f_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc_n(v_a_4109_, 2);
lean_dec_ref_known(v___x_4108_, 1);
v___f_4110_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4110_, 0, v___x_4099_);
lean_closure_set(v___f_4110_, 1, v_mvarId_4097_);
lean_closure_set(v___f_4110_, 2, v_a_4109_);
lean_closure_set(v___f_4110_, 3, v___x_4098_);
v___x_4111_ = lean_unsigned_to_nat(1u);
v___x_4112_ = lean_mk_empty_array_with_capacity(v___x_4111_);
v___x_4113_ = lean_array_push(v___x_4112_, v_a_4109_);
v___x_4114_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4113_, v_givenNames_4100_, v___f_4110_, v_config_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
return v___x_4114_;
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec(v_givenNames_4100_);
lean_dec_ref(v___x_4099_);
lean_dec(v___x_4098_);
lean_dec(v_mvarId_4097_);
v_a_4115_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4108_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4108_);
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
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_givenNames_4100_);
lean_dec_ref(v___x_4099_);
lean_dec(v___x_4098_);
lean_dec(v_mvarId_4097_);
v_a_4123_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4107_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4107_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4131_, lean_object* v___x_4132_, lean_object* v___x_4133_, lean_object* v_givenNames_4134_, lean_object* v_config_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4131_, v___x_4132_, v___x_4133_, v_givenNames_4134_, v_config_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec_ref(v_config_4135_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4145_, lean_object* v_givenNames_4146_, lean_object* v_config_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; 
v___x_4153_ = l_Lean_instInhabitedExpr;
v___x_4154_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4145_);
v___f_4155_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4155_, 0, v_mvarId_4145_);
lean_closure_set(v___f_4155_, 1, v___x_4154_);
lean_closure_set(v___f_4155_, 2, v___x_4153_);
lean_closure_set(v___f_4155_, 3, v_givenNames_4146_);
lean_closure_set(v___f_4155_, 4, v_config_4147_);
v___x_4156_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4145_, v___f_4155_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4157_, lean_object* v_givenNames_4158_, lean_object* v_config_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_MVarId_extractLets(v_mvarId_4157_, v_givenNames_4158_, v_config_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4166_, lean_object* v_val_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4166_, v_val_4167_, v___y_4169_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4174_, lean_object* v_val_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4174_, v_val_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4182_, lean_object* v_x_4183_, lean_object* v_x_4184_, lean_object* v_x_4185_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4183_, v_x_4184_, v_x_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4187_, lean_object* v_x_4188_, size_t v_x_4189_, size_t v_x_4190_, lean_object* v_x_4191_, lean_object* v_x_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4188_, v_x_4189_, v_x_4190_, v_x_4191_, v_x_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4194_, lean_object* v_x_4195_, lean_object* v_x_4196_, lean_object* v_x_4197_, lean_object* v_x_4198_, lean_object* v_x_4199_){
_start:
{
size_t v_x_2788__boxed_4200_; size_t v_x_2789__boxed_4201_; lean_object* v_res_4202_; 
v_x_2788__boxed_4200_ = lean_unbox_usize(v_x_4196_);
lean_dec(v_x_4196_);
v_x_2789__boxed_4201_ = lean_unbox_usize(v_x_4197_);
lean_dec(v_x_4197_);
v_res_4202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4194_, v_x_4195_, v_x_2788__boxed_4200_, v_x_2789__boxed_4201_, v_x_4198_, v_x_4199_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4203_, lean_object* v_n_4204_, lean_object* v_k_4205_, lean_object* v_v_4206_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4204_, v_k_4205_, v_v_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4208_, size_t v_depth_4209_, lean_object* v_keys_4210_, lean_object* v_vals_4211_, lean_object* v_heq_4212_, lean_object* v_i_4213_, lean_object* v_entries_4214_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4209_, v_keys_4210_, v_vals_4211_, v_i_4213_, v_entries_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4216_, lean_object* v_depth_4217_, lean_object* v_keys_4218_, lean_object* v_vals_4219_, lean_object* v_heq_4220_, lean_object* v_i_4221_, lean_object* v_entries_4222_){
_start:
{
size_t v_depth_boxed_4223_; lean_object* v_res_4224_; 
v_depth_boxed_4223_ = lean_unbox_usize(v_depth_4217_);
lean_dec(v_depth_4217_);
v_res_4224_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4216_, v_depth_boxed_4223_, v_keys_4218_, v_vals_4219_, v_heq_4220_, v_i_4221_, v_entries_4222_);
lean_dec_ref(v_vals_4219_);
lean_dec_ref(v_keys_4218_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4225_, lean_object* v_x_4226_, lean_object* v_x_4227_, lean_object* v_x_4228_, lean_object* v_x_4229_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4226_, v_x_4227_, v_x_4228_, v_x_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4231_, size_t v_i_4232_, lean_object* v_bs_4233_){
_start:
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_usize_dec_lt(v_i_4232_, v_sz_4231_);
if (v___x_4234_ == 0)
{
return v_bs_4233_;
}
else
{
lean_object* v_v_4235_; lean_object* v___x_4236_; lean_object* v_bs_x27_4237_; lean_object* v___x_4238_; size_t v___x_4239_; size_t v___x_4240_; lean_object* v___x_4241_; 
v_v_4235_ = lean_array_uget(v_bs_4233_, v_i_4232_);
v___x_4236_ = lean_unsigned_to_nat(0u);
v_bs_x27_4237_ = lean_array_uset(v_bs_4233_, v_i_4232_, v___x_4236_);
v___x_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_v_4235_);
v___x_4239_ = ((size_t)1ULL);
v___x_4240_ = lean_usize_add(v_i_4232_, v___x_4239_);
v___x_4241_ = lean_array_uset(v_bs_x27_4237_, v_i_4232_, v___x_4238_);
v_i_4232_ = v___x_4240_;
v_bs_4233_ = v___x_4241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4243_, lean_object* v_i_4244_, lean_object* v_bs_4245_){
_start:
{
size_t v_sz_boxed_4246_; size_t v_i_boxed_4247_; lean_object* v_res_4248_; 
v_sz_boxed_4246_ = lean_unbox_usize(v_sz_4243_);
lean_dec(v_sz_4243_);
v_i_boxed_4247_ = lean_unbox_usize(v_i_4244_);
lean_dec(v_i_4244_);
v_res_4248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4246_, v_i_boxed_4247_, v_bs_4245_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4249_, lean_object* v_fvars_4250_, lean_object* v_fvarIds_4251_, lean_object* v_givenNames_x27_4252_, lean_object* v_targetNew_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v___x_4259_; 
lean_inc(v_mvarId_4249_);
v___x_4259_ = l_Lean_MVarId_getTag(v_mvarId_4249_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4261_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4261_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4253_, v_a_4260_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; size_t v_sz_4263_; size_t v___x_4264_; lean_object* v___x_4265_; uint8_t v___x_4266_; uint8_t v___x_4267_; uint8_t v___x_4268_; lean_object* v___x_4269_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc_n(v_a_4262_, 2);
lean_dec_ref_known(v___x_4261_, 1);
v_sz_4263_ = lean_array_size(v_fvarIds_4251_);
v___x_4264_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4251_);
v___x_4265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4263_, v___x_4264_, v_fvarIds_4251_);
v___x_4266_ = 0;
v___x_4267_ = 1;
v___x_4268_ = 1;
v___x_4269_ = l_Lean_Meta_mkLetFVars(v___x_4265_, v_a_4262_, v___x_4266_, v___x_4267_, v___x_4268_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
lean_dec_ref(v___x_4265_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4284_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v___x_4269_, 1);
v___x_4271_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4249_, v_a_4270_, v___y_4255_);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4284_ == 0)
{
lean_object* v_unused_4285_; 
v_unused_4285_ = lean_ctor_get(v___x_4271_, 0);
lean_dec(v_unused_4285_);
v___x_4273_ = v___x_4271_;
v_isShared_4274_ = v_isSharedCheck_4284_;
goto v_resetjp_4272_;
}
else
{
lean_dec(v___x_4271_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4284_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4275_; size_t v_sz_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4282_; 
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v_fvarIds_4251_);
lean_ctor_set(v___x_4275_, 1, v_givenNames_x27_4252_);
v_sz_4276_ = lean_array_size(v_fvars_4250_);
v___x_4277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4276_, v___x_4264_, v_fvars_4250_);
v___x_4278_ = l_Lean_Expr_mvarId_x21(v_a_4262_);
lean_dec(v_a_4262_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4275_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v___x_4280_);
v___x_4282_ = v___x_4273_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_dec(v_a_4262_);
lean_dec(v_givenNames_x27_4252_);
lean_dec_ref(v_fvarIds_4251_);
lean_dec_ref(v_fvars_4250_);
lean_dec(v_mvarId_4249_);
v_a_4286_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4269_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4269_);
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
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_dec(v_givenNames_x27_4252_);
lean_dec_ref(v_fvarIds_4251_);
lean_dec_ref(v_fvars_4250_);
lean_dec(v_mvarId_4249_);
v_a_4294_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4261_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4261_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec_ref(v_targetNew_4253_);
lean_dec(v_givenNames_x27_4252_);
lean_dec_ref(v_fvarIds_4251_);
lean_dec_ref(v_fvars_4250_);
lean_dec(v_mvarId_4249_);
v_a_4302_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4259_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4259_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4310_, lean_object* v_fvars_4311_, lean_object* v_fvarIds_4312_, lean_object* v_givenNames_x27_4313_, lean_object* v_targetNew_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4310_, v_fvars_4311_, v_fvarIds_4312_, v_givenNames_x27_4313_, v_targetNew_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4321_, lean_object* v_binderName_4322_, lean_object* v_body_4323_, uint8_t v_binderInfo_4324_, lean_object* v___f_4325_, lean_object* v_binderType_4326_, lean_object* v___x_4327_, lean_object* v_mvarId_4328_, lean_object* v_fvarIds_4329_, lean_object* v_es_4330_, lean_object* v_givenNames_x27_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4342_; uint8_t v___x_4343_; 
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = lean_array_get_borrowed(v___x_4321_, v_es_4330_, v___x_4337_);
v___x_4342_ = lean_array_get_size(v_fvarIds_4329_);
v___x_4343_ = lean_nat_dec_eq(v___x_4342_, v___x_4337_);
if (v___x_4343_ == 0)
{
lean_dec(v_mvarId_4328_);
lean_dec(v___x_4327_);
goto v___jp_4339_;
}
else
{
uint8_t v___x_4344_; 
v___x_4344_ = lean_expr_eqv(v_binderType_4326_, v___x_4338_);
if (v___x_4344_ == 0)
{
lean_dec(v_mvarId_4328_);
lean_dec(v___x_4327_);
goto v___jp_4339_;
}
else
{
lean_object* v___x_4345_; 
v___x_4345_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4327_, v_mvarId_4328_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_dec_ref_known(v___x_4345_, 1);
goto v___jp_4339_;
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec(v_givenNames_x27_4331_);
lean_dec_ref(v_fvarIds_4329_);
lean_dec_ref(v___f_4325_);
lean_dec_ref(v_body_4323_);
lean_dec(v_binderName_4322_);
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4345_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4345_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
v___jp_4339_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
lean_inc(v___x_4338_);
v___x_4340_ = l_Lean_Expr_forallE___override(v_binderName_4322_, v___x_4338_, v_body_4323_, v_binderInfo_4324_);
lean_inc(v___y_4335_);
lean_inc_ref(v___y_4334_);
lean_inc(v___y_4333_);
lean_inc_ref(v___y_4332_);
v___x_4341_ = lean_apply_8(v___f_4325_, v_fvarIds_4329_, v_givenNames_x27_4331_, v___x_4340_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, lean_box(0));
return v___x_4341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4354_, lean_object* v_binderName_4355_, lean_object* v_body_4356_, lean_object* v_binderInfo_4357_, lean_object* v___f_4358_, lean_object* v_binderType_4359_, lean_object* v___x_4360_, lean_object* v_mvarId_4361_, lean_object* v_fvarIds_4362_, lean_object* v_es_4363_, lean_object* v_givenNames_x27_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
uint8_t v_binderInfo_1803__boxed_4370_; lean_object* v_res_4371_; 
v_binderInfo_1803__boxed_4370_ = lean_unbox(v_binderInfo_4357_);
v_res_4371_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4354_, v_binderName_4355_, v_body_4356_, v_binderInfo_1803__boxed_4370_, v___f_4358_, v_binderType_4359_, v___x_4360_, v_mvarId_4361_, v_fvarIds_4362_, v_es_4363_, v_givenNames_x27_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec_ref(v_es_4363_);
lean_dec_ref(v_binderType_4359_);
lean_dec_ref(v___x_4354_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4372_, lean_object* v_declName_4373_, lean_object* v_body_4374_, uint8_t v_nondep_4375_, lean_object* v___f_4376_, lean_object* v_type_4377_, lean_object* v_value_4378_, lean_object* v___x_4379_, lean_object* v_mvarId_4380_, lean_object* v_fvarIds_4381_, lean_object* v_es_4382_, lean_object* v_givenNames_x27_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4396_; uint8_t v___x_4397_; 
v___x_4389_ = lean_unsigned_to_nat(0u);
v___x_4390_ = lean_array_get_borrowed(v___x_4372_, v_es_4382_, v___x_4389_);
v___x_4391_ = lean_unsigned_to_nat(1u);
v___x_4392_ = lean_array_get_borrowed(v___x_4372_, v_es_4382_, v___x_4391_);
v___x_4396_ = lean_array_get_size(v_fvarIds_4381_);
v___x_4397_ = lean_nat_dec_eq(v___x_4396_, v___x_4389_);
if (v___x_4397_ == 0)
{
lean_dec(v_mvarId_4380_);
lean_dec(v___x_4379_);
goto v___jp_4393_;
}
else
{
uint8_t v___x_4398_; 
v___x_4398_ = lean_expr_eqv(v_type_4377_, v___x_4390_);
if (v___x_4398_ == 0)
{
lean_dec(v_mvarId_4380_);
lean_dec(v___x_4379_);
goto v___jp_4393_;
}
else
{
uint8_t v___x_4399_; 
v___x_4399_ = lean_expr_eqv(v_value_4378_, v___x_4392_);
if (v___x_4399_ == 0)
{
lean_dec(v_mvarId_4380_);
lean_dec(v___x_4379_);
goto v___jp_4393_;
}
else
{
lean_object* v___x_4400_; 
v___x_4400_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4379_, v_mvarId_4380_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_dec_ref_known(v___x_4400_, 1);
goto v___jp_4393_;
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_givenNames_x27_4383_);
lean_dec_ref(v_fvarIds_4381_);
lean_dec_ref(v___f_4376_);
lean_dec_ref(v_body_4374_);
lean_dec(v_declName_4373_);
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
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
}
v___jp_4393_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_inc(v___x_4392_);
lean_inc(v___x_4390_);
v___x_4394_ = l_Lean_Expr_letE___override(v_declName_4373_, v___x_4390_, v___x_4392_, v_body_4374_, v_nondep_4375_);
lean_inc(v___y_4387_);
lean_inc_ref(v___y_4386_);
lean_inc(v___y_4385_);
lean_inc_ref(v___y_4384_);
v___x_4395_ = lean_apply_8(v___f_4376_, v_fvarIds_4381_, v_givenNames_x27_4383_, v___x_4394_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, lean_box(0));
return v___x_4395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4409_ = _args[0];
lean_object* v_declName_4410_ = _args[1];
lean_object* v_body_4411_ = _args[2];
lean_object* v_nondep_4412_ = _args[3];
lean_object* v___f_4413_ = _args[4];
lean_object* v_type_4414_ = _args[5];
lean_object* v_value_4415_ = _args[6];
lean_object* v___x_4416_ = _args[7];
lean_object* v_mvarId_4417_ = _args[8];
lean_object* v_fvarIds_4418_ = _args[9];
lean_object* v_es_4419_ = _args[10];
lean_object* v_givenNames_x27_4420_ = _args[11];
lean_object* v___y_4421_ = _args[12];
lean_object* v___y_4422_ = _args[13];
lean_object* v___y_4423_ = _args[14];
lean_object* v___y_4424_ = _args[15];
lean_object* v___y_4425_ = _args[16];
_start:
{
uint8_t v_nondep_1874__boxed_4426_; lean_object* v_res_4427_; 
v_nondep_1874__boxed_4426_ = lean_unbox(v_nondep_4412_);
v_res_4427_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4409_, v_declName_4410_, v_body_4411_, v_nondep_1874__boxed_4426_, v___f_4413_, v_type_4414_, v_value_4415_, v___x_4416_, v_mvarId_4417_, v_fvarIds_4418_, v_es_4419_, v_givenNames_x27_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec_ref(v_es_4419_);
lean_dec_ref(v_value_4415_);
lean_dec_ref(v_type_4414_);
lean_dec_ref(v___x_4409_);
return v_res_4427_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4432_ = l_Lean_MessageData_ofFormat(v___x_4431_);
return v___x_4432_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4435_, lean_object* v___x_4436_, lean_object* v___f_4437_, lean_object* v___x_4438_, lean_object* v_givenNames_4439_, lean_object* v_config_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
lean_inc(v_mvarId_4435_);
v___x_4446_ = l_Lean_MVarId_getType(v_mvarId_4435_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
switch(lean_obj_tag(v_a_4447_))
{
case 7:
{
lean_object* v_binderName_4448_; lean_object* v_binderType_4449_; lean_object* v_body_4450_; uint8_t v_binderInfo_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v_binderName_4448_ = lean_ctor_get(v_a_4447_, 0);
lean_inc(v_binderName_4448_);
v_binderType_4449_ = lean_ctor_get(v_a_4447_, 1);
lean_inc_ref_n(v_binderType_4449_, 2);
v_body_4450_ = lean_ctor_get(v_a_4447_, 2);
lean_inc_ref(v_body_4450_);
v_binderInfo_4451_ = lean_ctor_get_uint8(v_a_4447_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4447_, 3);
v___x_4452_ = lean_box(v_binderInfo_4451_);
v___f_4453_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4453_, 0, v___x_4436_);
lean_closure_set(v___f_4453_, 1, v_binderName_4448_);
lean_closure_set(v___f_4453_, 2, v_body_4450_);
lean_closure_set(v___f_4453_, 3, v___x_4452_);
lean_closure_set(v___f_4453_, 4, v___f_4437_);
lean_closure_set(v___f_4453_, 5, v_binderType_4449_);
lean_closure_set(v___f_4453_, 6, v___x_4438_);
lean_closure_set(v___f_4453_, 7, v_mvarId_4435_);
v___x_4454_ = lean_unsigned_to_nat(1u);
v___x_4455_ = lean_mk_empty_array_with_capacity(v___x_4454_);
v___x_4456_ = lean_array_push(v___x_4455_, v_binderType_4449_);
v___x_4457_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4456_, v_givenNames_4439_, v___f_4453_, v_config_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4457_;
}
case 8:
{
lean_object* v_declName_4458_; lean_object* v_type_4459_; lean_object* v_value_4460_; lean_object* v_body_4461_; uint8_t v_nondep_4462_; lean_object* v___x_4463_; lean_object* v___f_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v_declName_4458_ = lean_ctor_get(v_a_4447_, 0);
lean_inc(v_declName_4458_);
v_type_4459_ = lean_ctor_get(v_a_4447_, 1);
lean_inc_ref_n(v_type_4459_, 2);
v_value_4460_ = lean_ctor_get(v_a_4447_, 2);
lean_inc_ref_n(v_value_4460_, 2);
v_body_4461_ = lean_ctor_get(v_a_4447_, 3);
lean_inc_ref(v_body_4461_);
v_nondep_4462_ = lean_ctor_get_uint8(v_a_4447_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4447_, 4);
v___x_4463_ = lean_box(v_nondep_4462_);
v___f_4464_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4464_, 0, v___x_4436_);
lean_closure_set(v___f_4464_, 1, v_declName_4458_);
lean_closure_set(v___f_4464_, 2, v_body_4461_);
lean_closure_set(v___f_4464_, 3, v___x_4463_);
lean_closure_set(v___f_4464_, 4, v___f_4437_);
lean_closure_set(v___f_4464_, 5, v_type_4459_);
lean_closure_set(v___f_4464_, 6, v_value_4460_);
lean_closure_set(v___f_4464_, 7, v___x_4438_);
lean_closure_set(v___f_4464_, 8, v_mvarId_4435_);
v___x_4465_ = lean_unsigned_to_nat(2u);
v___x_4466_ = lean_mk_empty_array_with_capacity(v___x_4465_);
v___x_4467_ = lean_array_push(v___x_4466_, v_type_4459_);
v___x_4468_ = lean_array_push(v___x_4467_, v_value_4460_);
v___x_4469_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4468_, v_givenNames_4439_, v___f_4464_, v_config_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4469_;
}
default: 
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_dec(v_a_4447_);
lean_dec(v_givenNames_4439_);
lean_dec_ref(v___f_4437_);
lean_dec_ref(v___x_4436_);
v___x_4470_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4471_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4438_, v_mvarId_4435_, v___x_4470_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4471_;
}
}
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
lean_dec(v_givenNames_4439_);
lean_dec(v___x_4438_);
lean_dec_ref(v___f_4437_);
lean_dec_ref(v___x_4436_);
lean_dec(v_mvarId_4435_);
v_a_4472_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4446_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4446_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4480_, lean_object* v___x_4481_, lean_object* v___f_4482_, lean_object* v___x_4483_, lean_object* v_givenNames_4484_, lean_object* v_config_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4480_, v___x_4481_, v___f_4482_, v___x_4483_, v_givenNames_4484_, v_config_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v_config_4485_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4492_, lean_object* v___x_4493_, lean_object* v_givenNames_4494_, lean_object* v_config_4495_, lean_object* v_mvarId_4496_, lean_object* v_fvars_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v___f_4503_; lean_object* v___f_4504_; lean_object* v___x_4505_; 
lean_inc_n(v_mvarId_4496_, 2);
v___f_4503_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4503_, 0, v_mvarId_4496_);
lean_closure_set(v___f_4503_, 1, v_fvars_4497_);
v___f_4504_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4504_, 0, v_mvarId_4496_);
lean_closure_set(v___f_4504_, 1, v___x_4492_);
lean_closure_set(v___f_4504_, 2, v___f_4503_);
lean_closure_set(v___f_4504_, 3, v___x_4493_);
lean_closure_set(v___f_4504_, 4, v_givenNames_4494_);
lean_closure_set(v___f_4504_, 5, v_config_4495_);
v___x_4505_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4496_, v___f_4504_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4506_, lean_object* v___x_4507_, lean_object* v_givenNames_4508_, lean_object* v_config_4509_, lean_object* v_mvarId_4510_, lean_object* v_fvars_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4506_, v___x_4507_, v_givenNames_4508_, v_config_4509_, v_mvarId_4510_, v_fvars_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4518_, lean_object* v_fvarId_4519_, lean_object* v_givenNames_4520_, lean_object* v_config_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___f_4529_; lean_object* v___x_4530_; 
v___x_4527_ = l_Lean_instInhabitedExpr;
v___x_4528_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
v___f_4529_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4529_, 0, v___x_4527_);
lean_closure_set(v___f_4529_, 1, v___x_4528_);
lean_closure_set(v___f_4529_, 2, v_givenNames_4520_);
lean_closure_set(v___f_4529_, 3, v_config_4521_);
lean_inc(v_mvarId_4518_);
v___x_4530_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4518_, v___x_4528_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; 
lean_dec_ref_known(v___x_4530_, 1);
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = lean_mk_empty_array_with_capacity(v___x_4531_);
v___x_4533_ = lean_array_push(v___x_4532_, v_fvarId_4519_);
v___x_4534_ = 0;
v___x_4535_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4518_, v___x_4533_, v___f_4529_, v___x_4534_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
return v___x_4535_;
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec_ref(v___f_4529_);
lean_dec(v_fvarId_4519_);
lean_dec(v_mvarId_4518_);
v_a_4536_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4530_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4530_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4544_, lean_object* v_fvarId_4545_, lean_object* v_givenNames_4546_, lean_object* v_config_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4544_, v_fvarId_4545_, v_givenNames_4546_, v_config_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4554_, lean_object* v___x_4555_, lean_object* v_config_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; 
lean_inc(v___x_4555_);
lean_inc(v_mvarId_4554_);
v___x_4562_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4554_, v___x_4555_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v___x_4563_; 
lean_dec_ref_known(v___x_4562_, 1);
lean_inc(v_mvarId_4554_);
v___x_4563_ = l_Lean_MVarId_getType(v_mvarId_4554_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4565_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc_n(v_a_4564_, 2);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4565_ = l_Lean_Meta_liftLets(v_a_4564_, v_config_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; uint8_t v___x_4567_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v___x_4567_ = lean_expr_eqv(v_a_4564_, v_a_4566_);
lean_dec(v_a_4564_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; 
lean_dec(v___x_4555_);
v___x_4568_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4554_, v_a_4566_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
return v___x_4568_;
}
else
{
lean_object* v___x_4569_; 
lean_inc(v_mvarId_4554_);
v___x_4569_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4555_, v_mvarId_4554_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v___x_4570_; 
lean_dec_ref_known(v___x_4569_, 1);
v___x_4570_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4554_, v_a_4566_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
return v___x_4570_;
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec(v_a_4566_);
lean_dec(v_mvarId_4554_);
v_a_4571_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4569_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4569_);
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
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v_a_4564_);
lean_dec(v___x_4555_);
lean_dec(v_mvarId_4554_);
v_a_4579_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4565_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4565_);
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
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec_ref(v_config_4556_);
lean_dec(v___x_4555_);
lean_dec(v_mvarId_4554_);
v_a_4587_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4563_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4563_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_dec_ref(v_config_4556_);
lean_dec(v___x_4555_);
lean_dec(v_mvarId_4554_);
v_a_4595_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4562_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4562_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4603_, lean_object* v___x_4604_, lean_object* v_config_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4603_, v___x_4604_, v_config_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4615_, lean_object* v_config_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
lean_object* v___x_4622_; lean_object* v___f_4623_; lean_object* v___x_4624_; 
v___x_4622_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4615_);
v___f_4623_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4623_, 0, v_mvarId_4615_);
lean_closure_set(v___f_4623_, 1, v___x_4622_);
lean_closure_set(v___f_4623_, 2, v_config_4616_);
v___x_4624_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4615_, v___f_4623_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4625_, lean_object* v_config_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Lean_MVarId_liftLets(v_mvarId_4625_, v_config_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4633_, lean_object* v_fvars_4634_, lean_object* v_targetNew_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v___x_4641_; 
v___x_4641_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4633_, v_targetNew_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4655_; 
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4644_ = v___x_4641_;
v_isShared_4645_ = v_isSharedCheck_4655_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4641_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4655_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4646_; size_t v_sz_4647_; size_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4653_; 
v___x_4646_ = lean_box(0);
v_sz_4647_ = lean_array_size(v_fvars_4634_);
v___x_4648_ = ((size_t)0ULL);
v___x_4649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4647_, v___x_4648_, v_fvars_4634_);
v___x_4650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
lean_ctor_set(v___x_4650_, 1, v_a_4642_);
v___x_4651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4646_);
lean_ctor_set(v___x_4651_, 1, v___x_4650_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 0, v___x_4651_);
v___x_4653_ = v___x_4644_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4651_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4663_; 
lean_dec_ref(v_fvars_4634_);
v_a_4656_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4658_ = v___x_4641_;
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4641_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
if (v_isShared_4659_ == 0)
{
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4664_, lean_object* v_fvars_4665_, lean_object* v_targetNew_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4664_, v_fvars_4665_, v_targetNew_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4673_, lean_object* v_config_4674_, lean_object* v___f_4675_, lean_object* v___x_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v___x_4682_; 
lean_inc(v_mvarId_4673_);
v___x_4682_ = l_Lean_MVarId_getType(v_mvarId_4673_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
lean_dec_ref_known(v___x_4682_, 1);
switch(lean_obj_tag(v_a_4683_))
{
case 7:
{
lean_object* v_binderName_4684_; lean_object* v_binderType_4685_; lean_object* v_body_4686_; uint8_t v_binderInfo_4687_; lean_object* v___x_4688_; 
v_binderName_4684_ = lean_ctor_get(v_a_4683_, 0);
lean_inc(v_binderName_4684_);
v_binderType_4685_ = lean_ctor_get(v_a_4683_, 1);
lean_inc_ref_n(v_binderType_4685_, 2);
v_body_4686_ = lean_ctor_get(v_a_4683_, 2);
lean_inc_ref(v_body_4686_);
v_binderInfo_4687_ = lean_ctor_get_uint8(v_a_4683_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4683_, 3);
v___x_4688_ = l_Lean_Meta_liftLets(v_binderType_4685_, v_config_4674_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___y_4694_; uint8_t v___x_4697_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v___x_4688_, 1);
v___x_4697_ = lean_expr_eqv(v_binderType_4685_, v_a_4689_);
lean_dec_ref(v_binderType_4685_);
if (v___x_4697_ == 0)
{
lean_dec(v___x_4676_);
lean_dec(v_mvarId_4673_);
v___y_4691_ = v___y_4677_;
v___y_4692_ = v___y_4678_;
v___y_4693_ = v___y_4679_;
v___y_4694_ = v___y_4680_;
goto v___jp_4690_;
}
else
{
lean_object* v___x_4698_; 
v___x_4698_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4676_, v_mvarId_4673_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_dec_ref_known(v___x_4698_, 1);
v___y_4691_ = v___y_4677_;
v___y_4692_ = v___y_4678_;
v___y_4693_ = v___y_4679_;
v___y_4694_ = v___y_4680_;
goto v___jp_4690_;
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
lean_dec(v_a_4689_);
lean_dec_ref(v_body_4686_);
lean_dec(v_binderName_4684_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec_ref(v___f_4675_);
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
v___jp_4690_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4695_ = l_Lean_Expr_forallE___override(v_binderName_4684_, v_a_4689_, v_body_4686_, v_binderInfo_4687_);
v___x_4696_ = lean_apply_6(v___f_4675_, v___x_4695_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, lean_box(0));
return v___x_4696_;
}
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
lean_dec_ref(v_body_4686_);
lean_dec_ref(v_binderType_4685_);
lean_dec(v_binderName_4684_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___x_4676_);
lean_dec_ref(v___f_4675_);
lean_dec(v_mvarId_4673_);
v_a_4707_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4709_ = v___x_4688_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4688_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
case 8:
{
lean_object* v_declName_4715_; lean_object* v_type_4716_; lean_object* v_value_4717_; lean_object* v_body_4718_; uint8_t v_nondep_4719_; lean_object* v___x_4720_; 
v_declName_4715_ = lean_ctor_get(v_a_4683_, 0);
lean_inc(v_declName_4715_);
v_type_4716_ = lean_ctor_get(v_a_4683_, 1);
lean_inc_ref_n(v_type_4716_, 2);
v_value_4717_ = lean_ctor_get(v_a_4683_, 2);
lean_inc_ref(v_value_4717_);
v_body_4718_ = lean_ctor_get(v_a_4683_, 3);
lean_inc_ref(v_body_4718_);
v_nondep_4719_ = lean_ctor_get_uint8(v_a_4683_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4683_, 4);
lean_inc_ref(v_config_4674_);
v___x_4720_ = l_Lean_Meta_liftLets(v_type_4716_, v_config_4674_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4722_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
lean_inc_ref(v_value_4717_);
v___x_4722_ = l_Lean_Meta_liftLets(v_value_4717_, v_config_4674_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; uint8_t v___y_4732_; uint8_t v___x_4742_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
v___x_4742_ = lean_expr_eqv(v_type_4716_, v_a_4721_);
lean_dec_ref(v_type_4716_);
if (v___x_4742_ == 0)
{
lean_dec_ref(v_value_4717_);
v___y_4732_ = v___x_4742_;
goto v___jp_4731_;
}
else
{
uint8_t v___x_4743_; 
v___x_4743_ = lean_expr_eqv(v_value_4717_, v_a_4723_);
lean_dec_ref(v_value_4717_);
v___y_4732_ = v___x_4743_;
goto v___jp_4731_;
}
v___jp_4724_:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4729_ = l_Lean_Expr_letE___override(v_declName_4715_, v_a_4721_, v_a_4723_, v_body_4718_, v_nondep_4719_);
v___x_4730_ = lean_apply_6(v___f_4675_, v___x_4729_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, lean_box(0));
return v___x_4730_;
}
v___jp_4731_:
{
if (v___y_4732_ == 0)
{
lean_dec(v___x_4676_);
lean_dec(v_mvarId_4673_);
v___y_4725_ = v___y_4677_;
v___y_4726_ = v___y_4678_;
v___y_4727_ = v___y_4679_;
v___y_4728_ = v___y_4680_;
goto v___jp_4724_;
}
else
{
lean_object* v___x_4733_; 
v___x_4733_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4676_, v_mvarId_4673_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_dec_ref_known(v___x_4733_, 1);
v___y_4725_ = v___y_4677_;
v___y_4726_ = v___y_4678_;
v___y_4727_ = v___y_4679_;
v___y_4728_ = v___y_4680_;
goto v___jp_4724_;
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
lean_dec(v_a_4723_);
lean_dec(v_a_4721_);
lean_dec_ref(v_body_4718_);
lean_dec(v_declName_4715_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec_ref(v___f_4675_);
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4733_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4733_);
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
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_a_4721_);
lean_dec_ref(v_body_4718_);
lean_dec_ref(v_value_4717_);
lean_dec_ref(v_type_4716_);
lean_dec(v_declName_4715_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___x_4676_);
lean_dec_ref(v___f_4675_);
lean_dec(v_mvarId_4673_);
v_a_4744_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4722_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4722_);
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
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec_ref(v_body_4718_);
lean_dec_ref(v_value_4717_);
lean_dec_ref(v_type_4716_);
lean_dec(v_declName_4715_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___x_4676_);
lean_dec_ref(v___f_4675_);
lean_dec_ref(v_config_4674_);
lean_dec(v_mvarId_4673_);
v_a_4752_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4720_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4720_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
default: 
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_dec(v_a_4683_);
lean_dec_ref(v___f_4675_);
lean_dec_ref(v_config_4674_);
v___x_4760_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4761_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4676_, v_mvarId_4673_, v___x_4760_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
return v___x_4761_;
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___x_4676_);
lean_dec_ref(v___f_4675_);
lean_dec_ref(v_config_4674_);
lean_dec(v_mvarId_4673_);
v_a_4762_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4682_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4682_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4770_, lean_object* v_config_4771_, lean_object* v___f_4772_, lean_object* v___x_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4770_, v_config_4771_, v___f_4772_, v___x_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4780_, lean_object* v___x_4781_, lean_object* v_mvarId_4782_, lean_object* v_fvars_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v___f_4789_; lean_object* v___f_4790_; lean_object* v___x_4791_; 
lean_inc_n(v_mvarId_4782_, 2);
v___f_4789_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4789_, 0, v_mvarId_4782_);
lean_closure_set(v___f_4789_, 1, v_fvars_4783_);
v___f_4790_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4790_, 0, v_mvarId_4782_);
lean_closure_set(v___f_4790_, 1, v_config_4780_);
lean_closure_set(v___f_4790_, 2, v___f_4789_);
lean_closure_set(v___f_4790_, 3, v___x_4781_);
v___x_4791_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4782_, v___f_4790_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4792_, lean_object* v___x_4793_, lean_object* v_mvarId_4794_, lean_object* v_fvars_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4792_, v___x_4793_, v_mvarId_4794_, v_fvars_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4802_, lean_object* v_fvarId_4803_, lean_object* v_config_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v___x_4810_; lean_object* v___f_4811_; lean_object* v___x_4812_; 
v___x_4810_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
v___f_4811_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4811_, 0, v_config_4804_);
lean_closure_set(v___f_4811_, 1, v___x_4810_);
lean_inc(v_mvarId_4802_);
v___x_4812_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4802_, v___x_4810_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; lean_object* v___x_4817_; 
lean_dec_ref_known(v___x_4812_, 1);
v___x_4813_ = lean_unsigned_to_nat(1u);
v___x_4814_ = lean_mk_empty_array_with_capacity(v___x_4813_);
v___x_4815_ = lean_array_push(v___x_4814_, v_fvarId_4803_);
v___x_4816_ = 0;
v___x_4817_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4802_, v___x_4815_, v___f_4811_, v___x_4816_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4826_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4826_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4826_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v_snd_4822_; lean_object* v___x_4824_; 
v_snd_4822_ = lean_ctor_get(v_a_4818_, 1);
lean_inc(v_snd_4822_);
lean_dec(v_a_4818_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v_snd_4822_);
v___x_4824_ = v___x_4820_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_snd_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
v_a_4827_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4817_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4817_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_dec_ref(v___f_4811_);
lean_dec(v_fvarId_4803_);
lean_dec(v_mvarId_4802_);
v_a_4835_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4812_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4812_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4843_, lean_object* v_fvarId_4844_, lean_object* v_config_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4843_, v_fvarId_4844_, v_config_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4852_, lean_object* v___x_4853_, uint8_t v_failIfUnchanged_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v___x_4860_; 
lean_inc(v___x_4853_);
lean_inc(v_mvarId_4852_);
v___x_4860_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4852_, v___x_4853_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v___x_4861_; 
lean_dec_ref_known(v___x_4860_, 1);
lean_inc(v_mvarId_4852_);
v___x_4861_ = l_Lean_MVarId_getType(v_mvarId_4852_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4863_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc_n(v_a_4862_, 2);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4863_ = l_Lean_Meta_letToHave(v_a_4862_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4863_) == 0)
{
if (v_failIfUnchanged_4854_ == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; 
lean_dec(v_a_4862_);
lean_dec(v___x_4853_);
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4852_, v_a_4864_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
return v___x_4865_;
}
else
{
lean_object* v_a_4866_; uint8_t v___x_4867_; 
v_a_4866_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4866_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4867_ = lean_expr_eqv(v_a_4862_, v_a_4866_);
lean_dec(v_a_4862_);
if (v___x_4867_ == 0)
{
lean_object* v___x_4868_; 
lean_dec(v___x_4853_);
v___x_4868_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4852_, v_a_4866_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
return v___x_4868_;
}
else
{
lean_object* v___x_4869_; 
lean_inc(v_mvarId_4852_);
v___x_4869_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4853_, v_mvarId_4852_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v___x_4870_; 
lean_dec_ref_known(v___x_4869_, 1);
v___x_4870_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4852_, v_a_4866_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
return v___x_4870_;
}
else
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
lean_dec(v_a_4866_);
lean_dec(v_mvarId_4852_);
v_a_4871_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4869_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4869_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
}
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
lean_dec(v_a_4862_);
lean_dec(v___x_4853_);
lean_dec(v_mvarId_4852_);
v_a_4879_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4863_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4863_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v___x_4853_);
lean_dec(v_mvarId_4852_);
v_a_4887_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4861_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4861_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec(v___x_4853_);
lean_dec(v_mvarId_4852_);
v_a_4895_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4860_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4860_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4903_, lean_object* v___x_4904_, lean_object* v_failIfUnchanged_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4911_; lean_object* v_res_4912_; 
v_failIfUnchanged_boxed_4911_ = lean_unbox(v_failIfUnchanged_4905_);
v_res_4912_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4903_, v___x_4904_, v_failIfUnchanged_boxed_4911_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4916_, uint8_t v_failIfUnchanged_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___f_4925_; lean_object* v___x_4926_; 
v___x_4923_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4924_ = lean_box(v_failIfUnchanged_4917_);
lean_inc(v_mvarId_4916_);
v___f_4925_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4925_, 0, v_mvarId_4916_);
lean_closure_set(v___f_4925_, 1, v___x_4923_);
lean_closure_set(v___f_4925_, 2, v___x_4924_);
v___x_4926_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4916_, v___f_4925_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4927_, lean_object* v_failIfUnchanged_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4934_; lean_object* v_res_4935_; 
v_failIfUnchanged_boxed_4934_ = lean_unbox(v_failIfUnchanged_4928_);
v_res_4935_ = l_Lean_MVarId_letToHave(v_mvarId_4927_, v_failIfUnchanged_boxed_4934_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4936_, lean_object* v___x_4937_, lean_object* v_fvarId_4938_, uint8_t v_failIfUnchanged_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
lean_object* v___x_4945_; 
lean_inc(v___x_4937_);
lean_inc(v_mvarId_4936_);
v___x_4945_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4936_, v___x_4937_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v___x_4946_; 
lean_dec_ref_known(v___x_4945_, 1);
lean_inc(v_fvarId_4938_);
v___x_4946_ = l_Lean_FVarId_getType___redArg(v_fvarId_4938_, v___y_4940_, v___y_4942_, v___y_4943_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4948_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc_n(v_a_4947_, 2);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4948_ = l_Lean_Meta_letToHave(v_a_4947_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
if (lean_obj_tag(v___x_4948_) == 0)
{
if (v_failIfUnchanged_4939_ == 0)
{
lean_object* v_a_4949_; lean_object* v___x_4950_; 
lean_dec(v_a_4947_);
lean_dec(v___x_4937_);
v_a_4949_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_a_4949_);
lean_dec_ref_known(v___x_4948_, 1);
v___x_4950_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4936_, v_fvarId_4938_, v_a_4949_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
return v___x_4950_;
}
else
{
lean_object* v_a_4951_; uint8_t v___x_4952_; 
v_a_4951_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_a_4951_);
lean_dec_ref_known(v___x_4948_, 1);
v___x_4952_ = lean_expr_eqv(v_a_4947_, v_a_4951_);
lean_dec(v_a_4947_);
if (v___x_4952_ == 0)
{
lean_object* v___x_4953_; 
lean_dec(v___x_4937_);
v___x_4953_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4936_, v_fvarId_4938_, v_a_4951_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
return v___x_4953_;
}
else
{
lean_object* v___x_4954_; 
lean_inc(v_mvarId_4936_);
v___x_4954_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4937_, v_mvarId_4936_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4955_; 
lean_dec_ref_known(v___x_4954_, 1);
v___x_4955_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4936_, v_fvarId_4938_, v_a_4951_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
return v___x_4955_;
}
else
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
lean_dec(v_a_4951_);
lean_dec(v_fvarId_4938_);
lean_dec(v_mvarId_4936_);
v_a_4956_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4954_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4954_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
lean_dec(v_a_4947_);
lean_dec(v_fvarId_4938_);
lean_dec(v___x_4937_);
lean_dec(v_mvarId_4936_);
v_a_4964_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4948_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4948_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4979_; 
lean_dec(v_fvarId_4938_);
lean_dec(v___x_4937_);
lean_dec(v_mvarId_4936_);
v_a_4972_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4974_ = v___x_4946_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4946_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
v___x_4977_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
return v___x_4977_;
}
}
}
}
else
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4987_; 
lean_dec(v_fvarId_4938_);
lean_dec(v___x_4937_);
lean_dec(v_mvarId_4936_);
v_a_4980_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4982_ = v___x_4945_;
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4945_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4985_; 
if (v_isShared_4983_ == 0)
{
v___x_4985_ = v___x_4982_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4980_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_4988_, lean_object* v___x_4989_, lean_object* v_fvarId_4990_, lean_object* v_failIfUnchanged_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4997_; lean_object* v_res_4998_; 
v_failIfUnchanged_boxed_4997_ = lean_unbox(v_failIfUnchanged_4991_);
v_res_4998_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_4988_, v___x_4989_, v_fvarId_4990_, v_failIfUnchanged_boxed_4997_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_4999_, lean_object* v_fvarId_5000_, uint8_t v_failIfUnchanged_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___f_5009_; lean_object* v___x_5010_; 
v___x_5007_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5008_ = lean_box(v_failIfUnchanged_5001_);
lean_inc(v_mvarId_4999_);
v___f_5009_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5009_, 0, v_mvarId_4999_);
lean_closure_set(v___f_5009_, 1, v___x_5007_);
lean_closure_set(v___f_5009_, 2, v_fvarId_5000_);
lean_closure_set(v___f_5009_, 3, v___x_5008_);
v___x_5010_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4999_, v___f_5009_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5011_, lean_object* v_fvarId_5012_, lean_object* v_failIfUnchanged_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5019_; lean_object* v_res_5020_; 
v_failIfUnchanged_boxed_5019_ = lean_unbox(v_failIfUnchanged_5013_);
v_res_5020_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5011_, v_fvarId_5012_, v_failIfUnchanged_boxed_5019_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
return v_res_5020_;
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
