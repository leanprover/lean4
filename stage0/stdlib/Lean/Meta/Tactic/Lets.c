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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
uint8_t v___x_1062_; 
v___x_1062_ = lean_nat_dec_le(v___x_1059_, v___x_1059_);
if (v___x_1062_ == 0)
{
if (v___x_1061_ == 0)
{
v___y_1051_ = v___x_1060_;
goto v___jp_1050_;
}
else
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = lean_usize_of_nat(v___x_1059_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1057_, v_decls_1040_, v___x_1063_, v___x_1064_, v___x_1060_);
v___y_1051_ = v___x_1065_;
goto v___jp_1050_;
}
}
else
{
size_t v___x_1066_; size_t v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = ((size_t)0ULL);
v___x_1067_ = lean_usize_of_nat(v___x_1059_);
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1057_, v_decls_1040_, v___x_1066_, v___x_1067_, v___x_1060_);
v___y_1051_ = v___x_1068_;
goto v___jp_1050_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object* v_decls_1069_, lean_object* v_k_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1069_, v_k_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec_ref(v_decls_1069_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_fvarId_1080_, lean_object* v_as_1081_, lean_object* v_j_1082_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_array_get_size(v_as_1081_);
v___x_1084_ = lean_nat_dec_lt(v_j_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_dec(v_j_1082_);
v___x_1085_ = lean_box(0);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v_decl_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1086_ = lean_array_fget_borrowed(v_as_1081_, v_j_1082_);
v_decl_1087_ = lean_ctor_get(v___x_1086_, 0);
v___x_1088_ = l_Lean_LocalDecl_fvarId(v_decl_1087_);
v___x_1089_ = l_Lean_instBEqFVarId_beq(v___x_1088_, v_fvarId_1080_);
lean_dec(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = lean_nat_add(v_j_1082_, v___x_1090_);
lean_dec(v_j_1082_);
v_j_1082_ = v___x_1091_;
goto _start;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_j_1082_);
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_fvarId_1094_, lean_object* v_as_1095_, lean_object* v_j_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1094_, v_as_1095_, v_j_1096_);
lean_dec_ref(v_as_1095_);
lean_dec(v_fvarId_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1098_, lean_object* v_k_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_lctx_1109_; uint8_t v___x_1110_; 
v___x_1108_ = lean_st_ref_get(v_a_1102_);
v_lctx_1109_ = lean_ctor_get(v_a_1103_, 2);
v___x_1110_ = l_Lean_LocalContext_contains(v_lctx_1109_, v_fvarId_1098_);
if (v___x_1110_ == 0)
{
lean_object* v_decls_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_decls_1111_ = lean_ctor_get(v___x_1108_, 1);
lean_inc_ref(v_decls_1111_);
lean_dec(v___x_1108_);
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1098_, v_decls_1111_, v___x_1112_);
if (lean_obj_tag(v___x_1113_) == 1)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_val_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_val_1114_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v_val_1114_, v___x_1115_);
lean_dec(v_val_1114_);
v___x_1117_ = l_Array_toSubarray___redArg(v_decls_1111_, v___x_1112_, v___x_1116_);
v___x_1118_ = l_Subarray_copy___redArg(v___x_1117_);
v___x_1119_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_1118_, v_k_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec_ref(v___x_1118_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; 
lean_dec(v___x_1113_);
lean_dec_ref(v_decls_1111_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc_ref(v_a_1100_);
v___x_1120_ = lean_apply_8(v_k_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, lean_box(0));
return v___x_1120_;
}
}
else
{
lean_object* v___x_1121_; 
lean_dec(v___x_1108_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc_ref(v_a_1100_);
v___x_1121_ = lean_apply_8(v_k_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, lean_box(0));
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1122_, lean_object* v_k_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1122_, v_k_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_fvarId_1122_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1133_, lean_object* v_fvarId_1134_, lean_object* v_k_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1134_, v_k_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_fvarId_1146_, lean_object* v_k_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1145_, v_fvarId_1146_, v_k_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_fvarId_1146_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object* v_00_u03b1_1157_, lean_object* v_decls_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1158_, v_x_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_decls_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_1169_, v_decls_1170_, v_x_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object* v_00_u03b1_1181_, lean_object* v_decls_1182_, lean_object* v_k_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1182_, v_k_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object* v_00_u03b1_1193_, lean_object* v_decls_1194_, lean_object* v_k_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_1193_, v_decls_1194_, v_k_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_decls_1194_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = l_Lean_Expr_hasMVar(v_e_1205_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_e_1205_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; lean_object* v_mctx_1211_; lean_object* v___x_1212_; lean_object* v_fst_1213_; lean_object* v_snd_1214_; lean_object* v___x_1215_; lean_object* v_cache_1216_; lean_object* v_zetaDeltaFVarIds_1217_; lean_object* v_postponed_1218_; lean_object* v_diag_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1228_; 
v___x_1210_ = lean_st_ref_get(v___y_1206_);
v_mctx_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_ref(v_mctx_1211_);
lean_dec(v___x_1210_);
v___x_1212_ = l_Lean_instantiateMVarsCore(v_mctx_1211_, v_e_1205_);
v_fst_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_fst_1213_);
v_snd_1214_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_snd_1214_);
lean_dec_ref(v___x_1212_);
v___x_1215_ = lean_st_ref_take(v___y_1206_);
v_cache_1216_ = lean_ctor_get(v___x_1215_, 1);
v_zetaDeltaFVarIds_1217_ = lean_ctor_get(v___x_1215_, 2);
v_postponed_1218_ = lean_ctor_get(v___x_1215_, 3);
v_diag_1219_ = lean_ctor_get(v___x_1215_, 4);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1215_, 0);
lean_dec(v_unused_1229_);
v___x_1221_ = v___x_1215_;
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_diag_1219_);
lean_inc(v_postponed_1218_);
lean_inc(v_zetaDeltaFVarIds_1217_);
lean_inc(v_cache_1216_);
lean_dec(v___x_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_snd_1214_);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_snd_1214_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_cache_1216_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_zetaDeltaFVarIds_1217_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_postponed_1218_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_diag_1219_);
v___x_1224_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_st_ref_set(v___y_1206_, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_fst_1213_);
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1230_, v___y_1231_);
lean_dec(v___y_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1234_, v___y_1239_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1254_, size_t v_i_1255_, size_t v_stop_1256_, lean_object* v_b_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_a_1267_; uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_eq(v_i_1255_, v_stop_1256_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_array_uget_borrowed(v_as_1254_, v_i_1255_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_box(0);
v_a_1267_ = v___x_1275_;
goto v___jp_1266_;
}
else
{
lean_object* v_val_1276_; uint8_t v___y_1278_; uint8_t v___x_1305_; 
v_val_1276_ = lean_ctor_get(v___x_1274_, 0);
v___x_1305_ = l_Lean_LocalDecl_isLet(v_val_1276_, v___x_1273_);
if (v___x_1305_ == 0)
{
v___y_1278_ = v___x_1305_;
goto v___jp_1277_;
}
else
{
uint8_t v___x_1306_; 
v___x_1306_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1276_);
if (v___x_1306_ == 0)
{
v___y_1278_ = v___x_1305_;
goto v___jp_1277_;
}
else
{
goto v___jp_1271_;
}
}
v___jp_1277_:
{
if (v___y_1278_ == 0)
{
goto v___jp_1271_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = l_Lean_LocalDecl_value(v_val_1276_, v___x_1273_);
v___x_1280_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1279_, v___y_1262_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v_givenNames_1283_; lean_object* v_decls_1284_; lean_object* v_valueMap_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1296_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = lean_st_ref_take(v___y_1260_);
v_givenNames_1283_ = lean_ctor_get(v___x_1282_, 0);
v_decls_1284_ = lean_ctor_get(v___x_1282_, 1);
v_valueMap_1285_ = lean_ctor_get(v___x_1282_, 2);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1287_ = v___x_1282_;
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_valueMap_1285_);
lean_inc(v_decls_1284_);
lean_inc(v_givenNames_1283_);
lean_dec(v___x_1282_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1289_ = l_Lean_LocalDecl_fvarId(v_val_1276_);
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1285_, v_a_1281_, v___x_1289_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 2, v___x_1290_);
v___x_1292_ = v___x_1287_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_givenNames_1283_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_decls_1284_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_st_ref_set(v___y_1260_, v___x_1292_);
v___x_1294_ = lean_box(0);
v_a_1267_ = v___x_1294_;
goto v___jp_1266_;
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_a_1297_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1280_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1280_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_b_1257_);
return v___x_1307_;
}
v___jp_1266_:
{
size_t v___x_1268_; size_t v___x_1269_; 
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_add(v_i_1255_, v___x_1268_);
v_i_1255_ = v___x_1269_;
v_b_1257_ = v_a_1267_;
goto _start;
}
v___jp_1271_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_box(0);
v_a_1267_ = v___x_1272_;
goto v___jp_1266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1308_, lean_object* v_i_1309_, lean_object* v_stop_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
size_t v_i_boxed_1320_; size_t v_stop_boxed_1321_; lean_object* v_res_1322_; 
v_i_boxed_1320_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_stop_boxed_1321_ = lean_unbox_usize(v_stop_1310_);
lean_dec(v_stop_1310_);
v_res_1322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1308_, v_i_boxed_1320_, v_stop_boxed_1321_, v_b_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v_as_1308_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1323_, size_t v_i_1324_, size_t v_stop_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_a_1336_; uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_eq(v_i_1324_, v_stop_1325_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_array_uget_borrowed(v_as_1323_, v_i_1324_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_box(0);
v_a_1336_ = v___x_1344_;
goto v___jp_1335_;
}
else
{
lean_object* v_val_1345_; uint8_t v___y_1347_; uint8_t v___x_1374_; 
v_val_1345_ = lean_ctor_get(v___x_1343_, 0);
v___x_1374_ = l_Lean_LocalDecl_isLet(v_val_1345_, v___x_1342_);
if (v___x_1374_ == 0)
{
v___y_1347_ = v___x_1374_;
goto v___jp_1346_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1345_);
if (v___x_1375_ == 0)
{
v___y_1347_ = v___x_1374_;
goto v___jp_1346_;
}
else
{
goto v___jp_1340_;
}
}
v___jp_1346_:
{
if (v___y_1347_ == 0)
{
goto v___jp_1340_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = l_Lean_LocalDecl_value(v_val_1345_, v___x_1342_);
v___x_1349_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1348_, v___y_1331_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v_givenNames_1352_; lean_object* v_decls_1353_; lean_object* v_valueMap_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1365_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = lean_st_ref_take(v___y_1329_);
v_givenNames_1352_ = lean_ctor_get(v___x_1351_, 0);
v_decls_1353_ = lean_ctor_get(v___x_1351_, 1);
v_valueMap_1354_ = lean_ctor_get(v___x_1351_, 2);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1356_ = v___x_1351_;
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_valueMap_1354_);
lean_inc(v_decls_1353_);
lean_inc(v_givenNames_1352_);
lean_dec(v___x_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1358_ = l_Lean_LocalDecl_fvarId(v_val_1345_);
v___x_1359_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1354_, v_a_1350_, v___x_1358_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 2, v___x_1359_);
v___x_1361_ = v___x_1356_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_givenNames_1352_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_decls_1353_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_st_ref_set(v___y_1329_, v___x_1361_);
v___x_1363_ = lean_box(0);
v_a_1336_ = v___x_1363_;
goto v___jp_1335_;
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1349_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1349_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_b_1326_);
return v___x_1376_;
}
v___jp_1335_:
{
size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1324_, v___x_1337_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1323_, v___x_1338_, v_stop_1325_, v_a_1336_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1339_;
}
v___jp_1340_:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_box(0);
v_a_1336_ = v___x_1341_;
goto v___jp_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1377_, lean_object* v_i_1378_, lean_object* v_stop_1379_, lean_object* v_b_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
size_t v_i_boxed_1389_; size_t v_stop_boxed_1390_; lean_object* v_res_1391_; 
v_i_boxed_1389_ = lean_unbox_usize(v_i_1378_);
lean_dec(v_i_1378_);
v_stop_boxed_1390_ = lean_unbox_usize(v_stop_1379_);
lean_dec(v_stop_1379_);
v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1377_, v_i_boxed_1389_, v_stop_boxed_1390_, v_b_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v_as_1377_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 0)
{
lean_object* v_cs_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1422_; 
v_cs_1401_ = lean_ctor_get(v_x_1392_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1392_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1403_ = v_x_1392_;
v_isShared_1404_ = v_isSharedCheck_1422_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_cs_1401_);
lean_dec(v_x_1392_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1422_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_array_get_size(v_cs_1401_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_nat_dec_lt(v___x_1405_, v___x_1406_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1410_; 
lean_dec_ref(v_cs_1401_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1407_);
v___x_1410_ = v___x_1403_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1407_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_le(v___x_1406_, v___x_1406_);
if (v___x_1412_ == 0)
{
if (v___x_1408_ == 0)
{
lean_object* v___x_1414_; 
lean_dec_ref(v_cs_1401_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1407_);
v___x_1414_ = v___x_1403_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1407_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
lean_del_object(v___x_1403_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1406_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1401_, v___x_1416_, v___x_1417_, v___x_1407_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec_ref(v_cs_1401_);
return v___x_1418_;
}
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
lean_del_object(v___x_1403_);
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1406_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1401_, v___x_1419_, v___x_1420_, v___x_1407_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec_ref(v_cs_1401_);
return v___x_1421_;
}
}
}
}
else
{
lean_object* v_vs_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1444_; 
v_vs_1423_ = lean_ctor_get(v_x_1392_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_x_1392_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1425_ = v_x_1392_;
v_isShared_1426_ = v_isSharedCheck_1444_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_vs_1423_);
lean_dec(v_x_1392_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1444_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_array_get_size(v_vs_1423_);
v___x_1429_ = lean_box(0);
v___x_1430_ = lean_nat_dec_lt(v___x_1427_, v___x_1428_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1432_; 
lean_dec_ref(v_vs_1423_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set_tag(v___x_1425_, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1429_);
v___x_1432_ = v___x_1425_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1429_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
else
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_nat_dec_le(v___x_1428_, v___x_1428_);
if (v___x_1434_ == 0)
{
if (v___x_1430_ == 0)
{
lean_object* v___x_1436_; 
lean_dec_ref(v_vs_1423_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set_tag(v___x_1425_, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1429_);
v___x_1436_ = v___x_1425_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1429_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
else
{
size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
lean_del_object(v___x_1425_);
v___x_1438_ = ((size_t)0ULL);
v___x_1439_ = lean_usize_of_nat(v___x_1428_);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1423_, v___x_1438_, v___x_1439_, v___x_1429_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec_ref(v_vs_1423_);
return v___x_1440_;
}
}
else
{
size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; 
lean_del_object(v___x_1425_);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = lean_usize_of_nat(v___x_1428_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1423_, v___x_1441_, v___x_1442_, v___x_1429_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec_ref(v_vs_1423_);
return v___x_1443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1445_, size_t v_i_1446_, size_t v_stop_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
lean_inc(v___x_1458_);
v___x_1459_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1458_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; size_t v___x_1461_; size_t v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_add(v_i_1446_, v___x_1461_);
v_i_1446_ = v___x_1462_;
v_b_1448_ = v_a_1460_;
goto _start;
}
else
{
return v___x_1459_;
}
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_b_1448_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1465_, lean_object* v_i_1466_, lean_object* v_stop_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
size_t v_i_boxed_1477_; size_t v_stop_boxed_1478_; lean_object* v_res_1479_; 
v_i_boxed_1477_ = lean_unbox_usize(v_i_1466_);
lean_dec(v_i_1466_);
v_stop_boxed_1478_ = lean_unbox_usize(v_stop_1467_);
lean_dec(v_stop_1467_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1465_, v_i_boxed_1477_, v_stop_boxed_1478_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v_as_1465_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_root_1499_; lean_object* v_tail_1500_; lean_object* v___x_1501_; 
v_root_1499_ = lean_ctor_get(v_t_1490_, 0);
lean_inc_ref(v_root_1499_);
v_tail_1500_ = lean_ctor_get(v_t_1490_, 1);
lean_inc_ref(v_tail_1500_);
lean_dec_ref(v_t_1490_);
v___x_1501_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1499_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1522_; 
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v___x_1501_, 0);
lean_dec(v_unused_1523_);
v___x_1503_ = v___x_1501_;
v_isShared_1504_ = v_isSharedCheck_1522_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v___x_1501_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1522_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = lean_array_get_size(v_tail_1500_);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_nat_dec_lt(v___x_1505_, v___x_1506_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref(v_tail_1500_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1507_);
v___x_1510_ = v___x_1503_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1507_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
else
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_le(v___x_1506_, v___x_1506_);
if (v___x_1512_ == 0)
{
if (v___x_1508_ == 0)
{
lean_object* v___x_1514_; 
lean_dec_ref(v_tail_1500_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1507_);
v___x_1514_ = v___x_1503_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1507_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
else
{
size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
lean_del_object(v___x_1503_);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_of_nat(v___x_1506_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1500_, v___x_1516_, v___x_1517_, v___x_1507_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec_ref(v_tail_1500_);
return v___x_1518_;
}
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
lean_del_object(v___x_1503_);
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1506_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1500_, v___x_1519_, v___x_1520_, v___x_1507_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec_ref(v_tail_1500_);
return v___x_1521_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1500_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1533_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1535_, size_t v_x_1536_, size_t v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_object* v_cs_1546_; lean_object* v___x_1547_; size_t v___x_1548_; lean_object* v_j_1549_; lean_object* v___x_1550_; size_t v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v_cs_1546_ = lean_ctor_get(v_x_1535_, 0);
lean_inc_ref(v_cs_1546_);
lean_dec_ref(v_x_1535_);
v___x_1547_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1548_ = lean_usize_shift_right(v_x_1536_, v_x_1537_);
v_j_1549_ = lean_usize_to_nat(v___x_1548_);
v___x_1550_ = lean_array_get_borrowed(v___x_1547_, v_cs_1546_, v_j_1549_);
v___x_1551_ = ((size_t)1ULL);
v___x_1552_ = lean_usize_shift_left(v___x_1551_, v_x_1537_);
v___x_1553_ = lean_usize_sub(v___x_1552_, v___x_1551_);
v___x_1554_ = lean_usize_land(v_x_1536_, v___x_1553_);
v___x_1555_ = ((size_t)5ULL);
v___x_1556_ = lean_usize_sub(v_x_1537_, v___x_1555_);
lean_inc(v___x_1550_);
v___x_1557_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1550_, v___x_1554_, v___x_1556_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1579_; 
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v___x_1557_, 0);
lean_dec(v_unused_1580_);
v___x_1559_ = v___x_1557_;
v_isShared_1560_ = v_isSharedCheck_1579_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v___x_1557_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1579_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = lean_nat_add(v_j_1549_, v___x_1561_);
lean_dec(v_j_1549_);
v___x_1563_ = lean_array_get_size(v_cs_1546_);
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_nat_dec_lt(v___x_1562_, v___x_1563_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1567_; 
lean_dec(v___x_1562_);
lean_dec_ref(v_cs_1546_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1564_);
v___x_1567_ = v___x_1559_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1564_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_le(v___x_1563_, v___x_1563_);
if (v___x_1569_ == 0)
{
if (v___x_1565_ == 0)
{
lean_object* v___x_1571_; 
lean_dec(v___x_1562_);
lean_dec_ref(v_cs_1546_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1564_);
v___x_1571_ = v___x_1559_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1564_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
else
{
size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1559_);
v___x_1573_ = lean_usize_of_nat(v___x_1562_);
lean_dec(v___x_1562_);
v___x_1574_ = lean_usize_of_nat(v___x_1563_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1546_, v___x_1573_, v___x_1574_, v___x_1564_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec_ref(v_cs_1546_);
return v___x_1575_;
}
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
lean_del_object(v___x_1559_);
v___x_1576_ = lean_usize_of_nat(v___x_1562_);
lean_dec(v___x_1562_);
v___x_1577_ = lean_usize_of_nat(v___x_1563_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1546_, v___x_1576_, v___x_1577_, v___x_1564_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec_ref(v_cs_1546_);
return v___x_1578_;
}
}
}
}
else
{
lean_dec(v_j_1549_);
lean_dec_ref(v_cs_1546_);
return v___x_1557_;
}
}
else
{
lean_object* v_vs_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1602_; 
v_vs_1581_ = lean_ctor_get(v_x_1535_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1535_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1583_ = v_x_1535_;
v_isShared_1584_ = v_isSharedCheck_1602_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_vs_1581_);
lean_dec(v_x_1535_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1602_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1585_ = lean_usize_to_nat(v_x_1536_);
v___x_1586_ = lean_array_get_size(v_vs_1581_);
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_nat_dec_lt(v___x_1585_, v___x_1586_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1590_; 
lean_dec(v___x_1585_);
lean_dec_ref(v_vs_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1587_);
v___x_1590_ = v___x_1583_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1587_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
else
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_nat_dec_le(v___x_1586_, v___x_1586_);
if (v___x_1592_ == 0)
{
if (v___x_1588_ == 0)
{
lean_object* v___x_1594_; 
lean_dec(v___x_1585_);
lean_dec_ref(v_vs_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1587_);
v___x_1594_ = v___x_1583_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1587_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
else
{
size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
lean_del_object(v___x_1583_);
v___x_1596_ = lean_usize_of_nat(v___x_1585_);
lean_dec(v___x_1585_);
v___x_1597_ = lean_usize_of_nat(v___x_1586_);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1581_, v___x_1596_, v___x_1597_, v___x_1587_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec_ref(v_vs_1581_);
return v___x_1598_;
}
}
else
{
size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
lean_del_object(v___x_1583_);
v___x_1599_ = lean_usize_of_nat(v___x_1585_);
lean_dec(v___x_1585_);
v___x_1600_ = lean_usize_of_nat(v___x_1586_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1581_, v___x_1599_, v___x_1600_, v___x_1587_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec_ref(v_vs_1581_);
return v___x_1601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
size_t v_x_10795__boxed_1614_; size_t v_x_10796__boxed_1615_; lean_object* v_res_1616_; 
v_x_10795__boxed_1614_ = lean_unbox_usize(v_x_1604_);
lean_dec(v_x_1604_);
v_x_10796__boxed_1615_ = lean_unbox_usize(v_x_1605_);
lean_dec(v_x_1605_);
v_res_1616_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1603_, v_x_10795__boxed_1614_, v_x_10796__boxed_1615_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1617_, lean_object* v_start_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_nat_dec_eq(v_start_1618_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v_root_1629_; lean_object* v_tail_1630_; size_t v_shift_1631_; lean_object* v_tailOff_1632_; uint8_t v___x_1633_; 
v_root_1629_ = lean_ctor_get(v_t_1617_, 0);
lean_inc_ref(v_root_1629_);
v_tail_1630_ = lean_ctor_get(v_t_1617_, 1);
lean_inc_ref(v_tail_1630_);
v_shift_1631_ = lean_ctor_get_usize(v_t_1617_, 4);
v_tailOff_1632_ = lean_ctor_get(v_t_1617_, 3);
lean_inc(v_tailOff_1632_);
lean_dec_ref(v_t_1617_);
v___x_1633_ = lean_nat_dec_le(v_tailOff_1632_, v_start_1618_);
if (v___x_1633_ == 0)
{
size_t v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v_tailOff_1632_);
v___x_1634_ = lean_usize_of_nat(v_start_1618_);
v___x_1635_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1629_, v___x_1634_, v_shift_1631_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1655_; 
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v___x_1635_, 0);
lean_dec(v_unused_1656_);
v___x_1637_ = v___x_1635_;
v_isShared_1638_ = v_isSharedCheck_1655_;
goto v_resetjp_1636_;
}
else
{
lean_dec(v___x_1635_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1655_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = lean_array_get_size(v_tail_1630_);
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_nat_dec_lt(v___x_1627_, v___x_1639_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1643_; 
lean_dec_ref(v_tail_1630_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1643_ = v___x_1637_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1640_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
else
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_le(v___x_1639_, v___x_1639_);
if (v___x_1645_ == 0)
{
if (v___x_1641_ == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v_tail_1630_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1647_ = v___x_1637_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1640_);
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
lean_del_object(v___x_1637_);
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = lean_usize_of_nat(v___x_1639_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1630_, v___x_1649_, v___x_1650_, v___x_1640_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec_ref(v_tail_1630_);
return v___x_1651_;
}
}
else
{
size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
lean_del_object(v___x_1637_);
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = lean_usize_of_nat(v___x_1639_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1630_, v___x_1652_, v___x_1653_, v___x_1640_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec_ref(v_tail_1630_);
return v___x_1654_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1630_);
return v___x_1635_;
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
lean_dec_ref(v_root_1629_);
v___x_1657_ = lean_nat_sub(v_start_1618_, v_tailOff_1632_);
lean_dec(v_tailOff_1632_);
v___x_1658_ = lean_array_get_size(v_tail_1630_);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_nat_dec_lt(v___x_1657_, v___x_1658_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_dec(v___x_1657_);
lean_dec_ref(v_tail_1630_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
return v___x_1661_;
}
else
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v___x_1658_, v___x_1658_);
if (v___x_1662_ == 0)
{
if (v___x_1660_ == 0)
{
lean_object* v___x_1663_; 
lean_dec(v___x_1657_);
lean_dec_ref(v_tail_1630_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1659_);
return v___x_1663_;
}
else
{
size_t v___x_1664_; size_t v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_usize_of_nat(v___x_1657_);
lean_dec(v___x_1657_);
v___x_1665_ = lean_usize_of_nat(v___x_1658_);
v___x_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1630_, v___x_1664_, v___x_1665_, v___x_1659_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec_ref(v_tail_1630_);
return v___x_1666_;
}
}
else
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_usize_of_nat(v___x_1657_);
lean_dec(v___x_1657_);
v___x_1668_ = lean_usize_of_nat(v___x_1658_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1630_, v___x_1667_, v___x_1668_, v___x_1659_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec_ref(v_tail_1630_);
return v___x_1669_;
}
}
}
}
else
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1617_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1671_, lean_object* v_start_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1671_, v_start_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_start_1672_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1682_, lean_object* v_start_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_decls_1692_; lean_object* v___x_1693_; 
v_decls_1692_ = lean_ctor_get(v_lctx_1682_, 1);
lean_inc_ref(v_decls_1692_);
lean_dec_ref(v_lctx_1682_);
v___x_1693_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1692_, v_start_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1694_, lean_object* v_start_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1694_, v_start_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v_start_1695_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_lctx_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_lctx_1713_ = lean_ctor_get(v_a_1708_, 2);
v___x_1714_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1713_);
v___x_1715_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1713_, v___x_1714_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1724_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1726_){
_start:
{
lean_object* v___f_1727_; lean_object* v___x_1728_; 
v___f_1727_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1728_ = lean_find_expr(v___f_1727_, v_e_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
uint8_t v___x_1729_; 
v___x_1729_ = 0;
return v___x_1729_;
}
else
{
uint8_t v___x_1730_; 
lean_dec_ref(v___x_1728_);
v___x_1730_ = 1;
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1731_){
_start:
{
uint8_t v_res_1732_; lean_object* v_r_1733_; 
v_res_1732_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1731_);
lean_dec_ref(v_e_1731_);
v_r_1733_ = lean_box(v_res_1732_);
return v_r_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
v___x_1744_ = lean_apply_9(v_k_1734_, v_b_1738_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, lean_box(0));
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v_b_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1756_, uint8_t v_bi_1757_, lean_object* v_type_1758_, lean_object* v_k_1759_, uint8_t v_kind_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___f_1769_; lean_object* v___x_1770_; 
lean_inc(v___y_1763_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1769_, 0, v_k_1759_);
lean_closure_set(v___f_1769_, 1, v___y_1761_);
lean_closure_set(v___f_1769_, 2, v___y_1762_);
lean_closure_set(v___f_1769_, 3, v___y_1763_);
v___x_1770_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1756_, v_bi_1757_, v_type_1758_, v___f_1769_, v_kind_1760_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1770_) == 0)
{
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1779_, lean_object* v_bi_1780_, lean_object* v_type_1781_, lean_object* v_k_1782_, lean_object* v_kind_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v_bi_boxed_1792_; uint8_t v_kind_boxed_1793_; lean_object* v_res_1794_; 
v_bi_boxed_1792_ = lean_unbox(v_bi_1780_);
v_kind_boxed_1793_ = lean_unbox(v_kind_1783_);
v_res_1794_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1779_, v_bi_boxed_1792_, v_type_1781_, v_k_1782_, v_kind_boxed_1793_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1795_, lean_object* v_name_1796_, uint8_t v_bi_1797_, lean_object* v_type_1798_, lean_object* v_k_1799_, uint8_t v_kind_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1796_, v_bi_1797_, v_type_1798_, v_k_1799_, v_kind_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1810_, lean_object* v_name_1811_, lean_object* v_bi_1812_, lean_object* v_type_1813_, lean_object* v_k_1814_, lean_object* v_kind_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v_bi_boxed_1824_; uint8_t v_kind_boxed_1825_; lean_object* v_res_1826_; 
v_bi_boxed_1824_ = lean_unbox(v_bi_1812_);
v_kind_boxed_1825_ = lean_unbox(v_kind_1815_);
v_res_1826_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1810_, v_name_1811_, v_bi_boxed_1824_, v_type_1813_, v_k_1814_, v_kind_boxed_1825_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1827_, lean_object* v_e_1828_, lean_object* v___f_1829_, lean_object* v_____r_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
if (v_types_1827_ == 0)
{
lean_object* v___x_1839_; 
lean_inc_ref(v_e_1828_);
v___x_1839_ = l_Lean_Meta_isType(v_e_1828_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1850_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1850_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1850_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_unbox(v_a_1840_);
lean_dec(v_a_1840_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_del_object(v___x_1842_);
lean_dec_ref(v_e_1828_);
v___x_1845_ = lean_box(0);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
v___x_1846_ = lean_apply_9(v___f_1829_, v___x_1845_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, lean_box(0));
return v___x_1846_;
}
else
{
lean_object* v___x_1848_; 
lean_dec_ref(v___f_1829_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_e_1828_);
v___x_1848_ = v___x_1842_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_e_1828_);
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
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___f_1829_);
lean_dec_ref(v_e_1828_);
v_a_1851_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1839_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1839_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec_ref(v_e_1828_);
v___x_1859_ = lean_box(0);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
v___x_1860_ = lean_apply_9(v___f_1829_, v___x_1859_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, lean_box(0));
return v___x_1860_;
}
}
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
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1875_, uint8_t v___y_1876_){
_start:
{
if (v___y_1875_ == 0)
{
if (v___y_1876_ == 0)
{
uint8_t v___x_1877_; 
v___x_1877_ = 1;
return v___x_1877_;
}
else
{
return v___y_1875_;
}
}
else
{
return v___y_1876_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___y_50699__boxed_1880_; uint8_t v___y_50700__boxed_1881_; uint8_t v_res_1882_; lean_object* v_r_1883_; 
v___y_50699__boxed_1880_ = lean_unbox(v___y_1878_);
v___y_50700__boxed_1881_ = lean_unbox(v___y_1879_);
v_res_1882_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_50699__boxed_1880_, v___y_50700__boxed_1881_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_instMonadEIO(lean_box(0));
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_toApplicative_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1975_; 
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1903_ = l_StateRefT_x27_instMonad___redArg(v___x_1902_);
v_toApplicative_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v___x_1903_, 1);
lean_dec(v_unused_1976_);
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1975_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_toApplicative_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1975_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_toFunctor_1908_; lean_object* v_toSeq_1909_; lean_object* v_toSeqLeft_1910_; lean_object* v_toSeqRight_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1973_; 
v_toFunctor_1908_ = lean_ctor_get(v_toApplicative_1904_, 0);
v_toSeq_1909_ = lean_ctor_get(v_toApplicative_1904_, 2);
v_toSeqLeft_1910_ = lean_ctor_get(v_toApplicative_1904_, 3);
v_toSeqRight_1911_ = lean_ctor_get(v_toApplicative_1904_, 4);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_toApplicative_1904_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_toApplicative_1904_, 1);
lean_dec(v_unused_1974_);
v___x_1913_ = v_toApplicative_1904_;
v_isShared_1914_ = v_isSharedCheck_1973_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_toSeqRight_1911_);
lean_inc(v_toSeqLeft_1910_);
lean_inc(v_toSeq_1909_);
lean_inc(v_toFunctor_1908_);
lean_dec(v_toApplicative_1904_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1973_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___f_1915_; lean_object* v___f_1916_; lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; lean_object* v___f_1920_; lean_object* v___f_1921_; lean_object* v___f_1922_; lean_object* v___x_1924_; 
v___f_1915_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1916_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1908_);
v___f_1917_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1917_, 0, v_toFunctor_1908_);
v___f_1918_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1918_, 0, v_toFunctor_1908_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___f_1917_);
lean_ctor_set(v___x_1919_, 1, v___f_1918_);
v___f_1920_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1920_, 0, v_toSeqRight_1911_);
v___f_1921_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1921_, 0, v_toSeqLeft_1910_);
v___f_1922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1922_, 0, v_toSeq_1909_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 4, v___f_1920_);
lean_ctor_set(v___x_1913_, 3, v___f_1921_);
lean_ctor_set(v___x_1913_, 2, v___f_1922_);
lean_ctor_set(v___x_1913_, 1, v___f_1915_);
lean_ctor_set(v___x_1913_, 0, v___x_1919_);
v___x_1924_ = v___x_1913_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___f_1915_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v___f_1922_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v___f_1921_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v___f_1920_);
v___x_1924_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___f_1916_);
lean_ctor_set(v___x_1906_, 0, v___x_1924_);
v___x_1926_ = v___x_1906_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___f_1916_);
v___x_1926_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v_toApplicative_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1969_; 
v___x_1927_ = l_StateRefT_x27_instMonad___redArg(v___x_1926_);
v_toApplicative_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1927_, 1);
lean_dec(v_unused_1970_);
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1969_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_toApplicative_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1969_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_toFunctor_1932_; lean_object* v_toSeq_1933_; lean_object* v_toSeqLeft_1934_; lean_object* v_toSeqRight_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1967_; 
v_toFunctor_1932_ = lean_ctor_get(v_toApplicative_1928_, 0);
v_toSeq_1933_ = lean_ctor_get(v_toApplicative_1928_, 2);
v_toSeqLeft_1934_ = lean_ctor_get(v_toApplicative_1928_, 3);
v_toSeqRight_1935_ = lean_ctor_get(v_toApplicative_1928_, 4);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_toApplicative_1928_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_toApplicative_1928_, 1);
lean_dec(v_unused_1968_);
v___x_1937_ = v_toApplicative_1928_;
v_isShared_1938_ = v_isSharedCheck_1967_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_toSeqRight_1935_);
lean_inc(v_toSeqLeft_1934_);
lean_inc(v_toSeq_1933_);
lean_inc(v_toFunctor_1932_);
lean_dec(v_toApplicative_1928_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1967_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___x_1955_; 
v___f_1939_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1940_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1940_, 0, v___f_1939_);
v___x_1941_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1942_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1942_, 0, v___f_1940_);
lean_closure_set(v___f_1942_, 1, v___x_1941_);
v___f_1943_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1944_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1945_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1945_, 0, v___f_1943_);
lean_closure_set(v___f_1945_, 1, v___x_1944_);
v___f_1946_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1947_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1932_);
v___f_1948_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1948_, 0, v_toFunctor_1932_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toFunctor_1932_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___f_1948_);
lean_ctor_set(v___x_1950_, 1, v___f_1949_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toSeqRight_1935_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toSeqLeft_1934_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeq_1933_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 4, v___f_1951_);
lean_ctor_set(v___x_1937_, 3, v___f_1952_);
lean_ctor_set(v___x_1937_, 2, v___f_1953_);
lean_ctor_set(v___x_1937_, 1, v___f_1946_);
lean_ctor_set(v___x_1937_, 0, v___x_1950_);
v___x_1955_ = v___x_1937_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___f_1946_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v___f_1953_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v___f_1952_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v___f_1951_);
v___x_1955_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v___f_1947_);
lean_ctor_set(v___x_1930_, 0, v___x_1955_);
v___x_1957_ = v___x_1930_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___f_1947_);
v___x_1957_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___x_47587__overap_1963_; lean_object* v___x_1964_; 
v___x_1958_ = l_StateRefT_x27_instMonad___redArg(v___x_1957_);
v___x_1959_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1901_, v___f_1942_, v___f_1945_, v___x_1958_);
v___x_1960_ = l_Lean_instInhabitedExpr;
v___x_1961_ = l_instInhabitedOfMonad___redArg(v___x_1959_, v___x_1960_);
v___f_1962_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1962_, 0, v___x_1961_);
v___x_47587__overap_1963_ = lean_panic_fn_borrowed(v___f_1962_, v_msg_1892_);
lean_dec_ref(v___f_1962_);
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
v___x_1964_ = lean_apply_8(v___x_47587__overap_1963_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, lean_box(0));
return v___x_1964_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderName_1987_, uint8_t v_binderInfo_1988_, lean_object* v_e_1989_, lean_object* v_binderType_1990_, lean_object* v_body_1991_, lean_object* v_t_1992_, lean_object* v_b_1993_){
_start:
{
uint8_t v___y_1995_; size_t v___x_1999_; size_t v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = lean_ptr_addr(v_binderType_1990_);
v___x_2000_ = lean_ptr_addr(v_t_1992_);
v___x_2001_ = lean_usize_dec_eq(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
v___y_1995_ = v___x_2001_;
goto v___jp_1994_;
}
else
{
size_t v___x_2002_; size_t v___x_2003_; uint8_t v___x_2004_; 
v___x_2002_ = lean_ptr_addr(v_body_1991_);
v___x_2003_ = lean_ptr_addr(v_b_1993_);
v___x_2004_ = lean_usize_dec_eq(v___x_2002_, v___x_2003_);
v___y_1995_ = v___x_2004_;
goto v___jp_1994_;
}
v___jp_1994_:
{
if (v___y_1995_ == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Expr_lam___override(v_binderName_1987_, v_t_1992_, v_b_1993_, v_binderInfo_1988_);
return v___x_1996_;
}
else
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1988_, v_binderInfo_1988_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Expr_lam___override(v_binderName_1987_, v_t_1992_, v_b_1993_, v_binderInfo_1988_);
return v___x_1998_;
}
else
{
lean_dec_ref(v_b_1993_);
lean_dec_ref(v_t_1992_);
lean_dec(v_binderName_1987_);
lean_inc_ref(v_e_1989_);
return v_e_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderName_2005_, lean_object* v_binderInfo_2006_, lean_object* v_e_2007_, lean_object* v_binderType_2008_, lean_object* v_body_2009_, lean_object* v_t_2010_, lean_object* v_b_2011_){
_start:
{
uint8_t v_binderInfo_50886__boxed_2012_; lean_object* v_res_2013_; 
v_binderInfo_50886__boxed_2012_ = lean_unbox(v_binderInfo_2006_);
v_res_2013_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderName_2005_, v_binderInfo_50886__boxed_2012_, v_e_2007_, v_binderType_2008_, v_body_2009_, v_t_2010_, v_b_2011_);
lean_dec_ref(v_body_2009_);
lean_dec_ref(v_binderType_2008_);
lean_dec_ref(v_e_2007_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderName_2014_, uint8_t v_binderInfo_2015_, lean_object* v_e_2016_, lean_object* v_binderType_2017_, lean_object* v_body_2018_, lean_object* v_t_2019_, lean_object* v_b_2020_){
_start:
{
uint8_t v___y_2022_; size_t v___x_2026_; size_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2026_ = lean_ptr_addr(v_binderType_2017_);
v___x_2027_ = lean_ptr_addr(v_t_2019_);
v___x_2028_ = lean_usize_dec_eq(v___x_2026_, v___x_2027_);
if (v___x_2028_ == 0)
{
v___y_2022_ = v___x_2028_;
goto v___jp_2021_;
}
else
{
size_t v___x_2029_; size_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2029_ = lean_ptr_addr(v_body_2018_);
v___x_2030_ = lean_ptr_addr(v_b_2020_);
v___x_2031_ = lean_usize_dec_eq(v___x_2029_, v___x_2030_);
v___y_2022_ = v___x_2031_;
goto v___jp_2021_;
}
v___jp_2021_:
{
if (v___y_2022_ == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Expr_forallE___override(v_binderName_2014_, v_t_2019_, v_b_2020_, v_binderInfo_2015_);
return v___x_2023_;
}
else
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2015_, v_binderInfo_2015_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Expr_forallE___override(v_binderName_2014_, v_t_2019_, v_b_2020_, v_binderInfo_2015_);
return v___x_2025_;
}
else
{
lean_dec_ref(v_b_2020_);
lean_dec_ref(v_t_2019_);
lean_dec(v_binderName_2014_);
lean_inc_ref(v_e_2016_);
return v_e_2016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderName_2032_, lean_object* v_binderInfo_2033_, lean_object* v_e_2034_, lean_object* v_binderType_2035_, lean_object* v_body_2036_, lean_object* v_t_2037_, lean_object* v_b_2038_){
_start:
{
uint8_t v_binderInfo_50920__boxed_2039_; lean_object* v_res_2040_; 
v_binderInfo_50920__boxed_2039_ = lean_unbox(v_binderInfo_2033_);
v_res_2040_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderName_2032_, v_binderInfo_50920__boxed_2039_, v_e_2034_, v_binderType_2035_, v_body_2036_, v_t_2037_, v_b_2038_);
lean_dec_ref(v_body_2036_);
lean_dec_ref(v_binderType_2035_);
lean_dec_ref(v_e_2034_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_2041_, lean_object* v_type_2042_, lean_object* v_val_2043_, lean_object* v_k_2044_, uint8_t v_nondep_2045_, uint8_t v_kind_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___f_2055_; lean_object* v___x_2056_; 
lean_inc(v___y_2049_);
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
v___f_2055_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2055_, 0, v_k_2044_);
lean_closure_set(v___f_2055_, 1, v___y_2047_);
lean_closure_set(v___f_2055_, 2, v___y_2048_);
lean_closure_set(v___f_2055_, 3, v___y_2049_);
v___x_2056_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2041_, v_type_2042_, v_val_2043_, v___f_2055_, v_nondep_2045_, v_kind_2046_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2056_) == 0)
{
return v___x_2056_;
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2065_, lean_object* v_type_2066_, lean_object* v_val_2067_, lean_object* v_k_2068_, lean_object* v_nondep_2069_, lean_object* v_kind_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_nondep_boxed_2079_; uint8_t v_kind_boxed_2080_; lean_object* v_res_2081_; 
v_nondep_boxed_2079_ = lean_unbox(v_nondep_2069_);
v_kind_boxed_2080_ = lean_unbox(v_kind_2070_);
v_res_2081_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2065_, v_type_2066_, v_val_2067_, v_k_2068_, v_nondep_boxed_2079_, v_kind_boxed_2080_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2082_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = l_Lean_instInhabitedExpr;
v___x_2084_ = lean_panic_fn_borrowed(v___x_2083_, v_msg_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_box(0);
return v___x_2087_;
}
else
{
lean_object* v_key_2088_; lean_object* v_value_2089_; lean_object* v_tail_2090_; uint8_t v___x_2091_; 
v_key_2088_ = lean_ctor_get(v_x_2086_, 0);
v_value_2089_ = lean_ctor_get(v_x_2086_, 1);
v_tail_2090_ = lean_ctor_get(v_x_2086_, 2);
v___x_2091_ = l_Lean_ExprStructEq_beq(v_key_2088_, v_a_2085_);
if (v___x_2091_ == 0)
{
v_x_2086_ = v_tail_2090_;
goto _start;
}
else
{
lean_object* v___x_2093_; 
lean_inc(v_value_2089_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_value_2089_);
return v___x_2093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2094_, lean_object* v_x_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2094_, v_x_2095_);
lean_dec(v_x_2095_);
lean_dec_ref(v_a_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_buckets_2099_; lean_object* v___x_2100_; uint64_t v___x_2101_; uint64_t v___x_2102_; uint64_t v___x_2103_; uint64_t v_fold_2104_; uint64_t v___x_2105_; uint64_t v___x_2106_; uint64_t v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_buckets_2099_ = lean_ctor_get(v_m_2097_, 1);
v___x_2100_ = lean_array_get_size(v_buckets_2099_);
v___x_2101_ = l_Lean_ExprStructEq_hash(v_a_2098_);
v___x_2102_ = 32ULL;
v___x_2103_ = lean_uint64_shift_right(v___x_2101_, v___x_2102_);
v_fold_2104_ = lean_uint64_xor(v___x_2101_, v___x_2103_);
v___x_2105_ = 16ULL;
v___x_2106_ = lean_uint64_shift_right(v_fold_2104_, v___x_2105_);
v___x_2107_ = lean_uint64_xor(v_fold_2104_, v___x_2106_);
v___x_2108_ = lean_uint64_to_usize(v___x_2107_);
v___x_2109_ = lean_usize_of_nat(v___x_2100_);
v___x_2110_ = ((size_t)1ULL);
v___x_2111_ = lean_usize_sub(v___x_2109_, v___x_2110_);
v___x_2112_ = lean_usize_land(v___x_2108_, v___x_2111_);
v___x_2113_ = lean_array_uget_borrowed(v_buckets_2099_, v___x_2112_);
v___x_2114_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2098_, v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2115_, v_a_2116_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_m_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2118_, lean_object* v_x_2119_){
_start:
{
if (lean_obj_tag(v_x_2119_) == 0)
{
uint8_t v___x_2120_; 
v___x_2120_ = 0;
return v___x_2120_;
}
else
{
lean_object* v_key_2121_; lean_object* v_tail_2122_; lean_object* v_fst_2123_; lean_object* v_snd_2124_; lean_object* v_fst_2125_; lean_object* v_snd_2126_; uint8_t v___x_2130_; 
v_key_2121_ = lean_ctor_get(v_x_2119_, 0);
v_tail_2122_ = lean_ctor_get(v_x_2119_, 2);
v_fst_2123_ = lean_ctor_get(v_key_2121_, 0);
v_snd_2124_ = lean_ctor_get(v_key_2121_, 1);
v_fst_2125_ = lean_ctor_get(v_a_2118_, 0);
v_snd_2126_ = lean_ctor_get(v_a_2118_, 1);
v___x_2130_ = lean_unbox(v_fst_2123_);
if (v___x_2130_ == 0)
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_unbox(v_fst_2125_);
if (v___x_2131_ == 0)
{
goto v___jp_2127_;
}
else
{
v_x_2119_ = v_tail_2122_;
goto _start;
}
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_unbox(v_fst_2125_);
if (v___x_2133_ == 0)
{
v_x_2119_ = v_tail_2122_;
goto _start;
}
else
{
goto v___jp_2127_;
}
}
v___jp_2127_:
{
uint8_t v___x_2128_; 
v___x_2128_ = l_Lean_ExprStructEq_beq(v_snd_2124_, v_snd_2126_);
if (v___x_2128_ == 0)
{
v_x_2119_ = v_tail_2122_;
goto _start;
}
else
{
return v___x_2128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2135_, lean_object* v_x_2136_){
_start:
{
uint8_t v_res_2137_; lean_object* v_r_2138_; 
v_res_2137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2135_, v_x_2136_);
lean_dec(v_x_2136_);
lean_dec_ref(v_a_2135_);
v_r_2138_ = lean_box(v_res_2137_);
return v_r_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2139_, lean_object* v_b_2140_, lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
lean_dec(v_b_2140_);
lean_dec_ref(v_a_2139_);
return v_x_2141_;
}
else
{
lean_object* v_key_2142_; lean_object* v_value_2143_; lean_object* v_tail_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2163_; 
v_key_2142_ = lean_ctor_get(v_x_2141_, 0);
v_value_2143_ = lean_ctor_get(v_x_2141_, 1);
v_tail_2144_ = lean_ctor_get(v_x_2141_, 2);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2146_ = v_x_2141_;
v_isShared_2147_ = v_isSharedCheck_2163_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_tail_2144_);
lean_inc(v_value_2143_);
lean_inc(v_key_2142_);
lean_dec(v_x_2141_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2163_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_fst_2153_; lean_object* v_snd_2154_; lean_object* v_fst_2155_; lean_object* v_snd_2156_; uint8_t v___x_2160_; 
v_fst_2153_ = lean_ctor_get(v_key_2142_, 0);
v_snd_2154_ = lean_ctor_get(v_key_2142_, 1);
v_fst_2155_ = lean_ctor_get(v_a_2139_, 0);
v_snd_2156_ = lean_ctor_get(v_a_2139_, 1);
v___x_2160_ = lean_unbox(v_fst_2153_);
if (v___x_2160_ == 0)
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_unbox(v_fst_2155_);
if (v___x_2161_ == 0)
{
goto v___jp_2157_;
}
else
{
goto v___jp_2148_;
}
}
else
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_unbox(v_fst_2155_);
if (v___x_2162_ == 0)
{
goto v___jp_2148_;
}
else
{
goto v___jp_2157_;
}
}
v___jp_2148_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2139_, v_b_2140_, v_tail_2144_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 2, v___x_2149_);
v___x_2151_ = v___x_2146_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_key_2142_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_value_2143_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
v___jp_2157_:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_ExprStructEq_beq(v_snd_2154_, v_snd_2156_);
if (v___x_2158_ == 0)
{
goto v___jp_2148_;
}
else
{
lean_object* v___x_2159_; 
lean_del_object(v___x_2146_);
lean_dec(v_value_2143_);
lean_dec(v_key_2142_);
v___x_2159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2159_, 0, v_a_2139_);
lean_ctor_set(v___x_2159_, 1, v_b_2140_);
lean_ctor_set(v___x_2159_, 2, v_tail_2144_);
return v___x_2159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
if (lean_obj_tag(v_x_2165_) == 0)
{
return v_x_2164_;
}
else
{
lean_object* v_key_2166_; lean_object* v_value_2167_; lean_object* v_tail_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2199_; 
v_key_2166_ = lean_ctor_get(v_x_2165_, 0);
v_value_2167_ = lean_ctor_get(v_x_2165_, 1);
v_tail_2168_ = lean_ctor_get(v_x_2165_, 2);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_x_2165_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2170_ = v_x_2165_;
v_isShared_2171_ = v_isSharedCheck_2199_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_tail_2168_);
lean_inc(v_value_2167_);
lean_inc(v_key_2166_);
lean_dec(v_x_2165_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2199_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; uint64_t v___y_2176_; uint8_t v___x_2196_; 
v_fst_2172_ = lean_ctor_get(v_key_2166_, 0);
v_snd_2173_ = lean_ctor_get(v_key_2166_, 1);
v___x_2174_ = lean_array_get_size(v_x_2164_);
v___x_2196_ = lean_unbox(v_fst_2172_);
if (v___x_2196_ == 0)
{
uint64_t v___x_2197_; 
v___x_2197_ = 13ULL;
v___y_2176_ = v___x_2197_;
goto v___jp_2175_;
}
else
{
uint64_t v___x_2198_; 
v___x_2198_ = 11ULL;
v___y_2176_ = v___x_2198_;
goto v___jp_2175_;
}
v___jp_2175_:
{
uint64_t v___x_2177_; uint64_t v___x_2178_; uint64_t v___x_2179_; uint64_t v___x_2180_; uint64_t v_fold_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; size_t v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2177_ = l_Lean_ExprStructEq_hash(v_snd_2173_);
v___x_2178_ = lean_uint64_mix_hash(v___y_2176_, v___x_2177_);
v___x_2179_ = 32ULL;
v___x_2180_ = lean_uint64_shift_right(v___x_2178_, v___x_2179_);
v_fold_2181_ = lean_uint64_xor(v___x_2178_, v___x_2180_);
v___x_2182_ = 16ULL;
v___x_2183_ = lean_uint64_shift_right(v_fold_2181_, v___x_2182_);
v___x_2184_ = lean_uint64_xor(v_fold_2181_, v___x_2183_);
v___x_2185_ = lean_uint64_to_usize(v___x_2184_);
v___x_2186_ = lean_usize_of_nat(v___x_2174_);
v___x_2187_ = ((size_t)1ULL);
v___x_2188_ = lean_usize_sub(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_usize_land(v___x_2185_, v___x_2188_);
v___x_2190_ = lean_array_uget_borrowed(v_x_2164_, v___x_2189_);
lean_inc(v___x_2190_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 2, v___x_2190_);
v___x_2192_ = v___x_2170_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_key_2166_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_value_2167_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_array_uset(v_x_2164_, v___x_2189_, v___x_2192_);
v_x_2164_ = v___x_2193_;
v_x_2165_ = v_tail_2168_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2200_, lean_object* v_source_2201_, lean_object* v_target_2202_){
_start:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = lean_array_get_size(v_source_2201_);
v___x_2204_ = lean_nat_dec_lt(v_i_2200_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_dec_ref(v_source_2201_);
lean_dec(v_i_2200_);
return v_target_2202_;
}
else
{
lean_object* v_es_2205_; lean_object* v___x_2206_; lean_object* v_source_2207_; lean_object* v_target_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_es_2205_ = lean_array_fget(v_source_2201_, v_i_2200_);
v___x_2206_ = lean_box(0);
v_source_2207_ = lean_array_fset(v_source_2201_, v_i_2200_, v___x_2206_);
v_target_2208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2202_, v_es_2205_);
v___x_2209_ = lean_unsigned_to_nat(1u);
v___x_2210_ = lean_nat_add(v_i_2200_, v___x_2209_);
lean_dec(v_i_2200_);
v_i_2200_ = v___x_2210_;
v_source_2201_ = v_source_2207_;
v_target_2202_ = v_target_2208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2212_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v_nbuckets_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2213_ = lean_array_get_size(v_data_2212_);
v___x_2214_ = lean_unsigned_to_nat(2u);
v_nbuckets_2215_ = lean_nat_mul(v___x_2213_, v___x_2214_);
v___x_2216_ = lean_unsigned_to_nat(0u);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_mk_array(v_nbuckets_2215_, v___x_2217_);
v___x_2219_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2216_, v_data_2212_, v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2220_, lean_object* v_a_2221_, lean_object* v_b_2222_){
_start:
{
lean_object* v_size_2223_; lean_object* v_buckets_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2275_; 
v_size_2223_ = lean_ctor_get(v_m_2220_, 0);
v_buckets_2224_ = lean_ctor_get(v_m_2220_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_m_2220_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2226_ = v_m_2220_;
v_isShared_2227_ = v_isSharedCheck_2275_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_buckets_2224_);
lean_inc(v_size_2223_);
lean_dec(v_m_2220_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2275_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2230_; uint64_t v___y_2232_; uint8_t v___x_2272_; 
v_fst_2228_ = lean_ctor_get(v_a_2221_, 0);
v_snd_2229_ = lean_ctor_get(v_a_2221_, 1);
v___x_2230_ = lean_array_get_size(v_buckets_2224_);
v___x_2272_ = lean_unbox(v_fst_2228_);
if (v___x_2272_ == 0)
{
uint64_t v___x_2273_; 
v___x_2273_ = 13ULL;
v___y_2232_ = v___x_2273_;
goto v___jp_2231_;
}
else
{
uint64_t v___x_2274_; 
v___x_2274_ = 11ULL;
v___y_2232_ = v___x_2274_;
goto v___jp_2231_;
}
v___jp_2231_:
{
uint64_t v___x_2233_; uint64_t v___x_2234_; uint64_t v___x_2235_; uint64_t v___x_2236_; uint64_t v_fold_2237_; uint64_t v___x_2238_; uint64_t v___x_2239_; uint64_t v___x_2240_; size_t v___x_2241_; size_t v___x_2242_; size_t v___x_2243_; size_t v___x_2244_; size_t v___x_2245_; lean_object* v_bkt_2246_; uint8_t v___x_2247_; 
v___x_2233_ = l_Lean_ExprStructEq_hash(v_snd_2229_);
v___x_2234_ = lean_uint64_mix_hash(v___y_2232_, v___x_2233_);
v___x_2235_ = 32ULL;
v___x_2236_ = lean_uint64_shift_right(v___x_2234_, v___x_2235_);
v_fold_2237_ = lean_uint64_xor(v___x_2234_, v___x_2236_);
v___x_2238_ = 16ULL;
v___x_2239_ = lean_uint64_shift_right(v_fold_2237_, v___x_2238_);
v___x_2240_ = lean_uint64_xor(v_fold_2237_, v___x_2239_);
v___x_2241_ = lean_uint64_to_usize(v___x_2240_);
v___x_2242_ = lean_usize_of_nat(v___x_2230_);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_sub(v___x_2242_, v___x_2243_);
v___x_2245_ = lean_usize_land(v___x_2241_, v___x_2244_);
v_bkt_2246_ = lean_array_uget_borrowed(v_buckets_2224_, v___x_2245_);
v___x_2247_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2221_, v_bkt_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v_size_x27_2249_; lean_object* v___x_2250_; lean_object* v_buckets_x27_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v_size_x27_2249_ = lean_nat_add(v_size_2223_, v___x_2248_);
lean_dec(v_size_2223_);
lean_inc(v_bkt_2246_);
v___x_2250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2250_, 0, v_a_2221_);
lean_ctor_set(v___x_2250_, 1, v_b_2222_);
lean_ctor_set(v___x_2250_, 2, v_bkt_2246_);
v_buckets_x27_2251_ = lean_array_uset(v_buckets_2224_, v___x_2245_, v___x_2250_);
v___x_2252_ = lean_unsigned_to_nat(4u);
v___x_2253_ = lean_nat_mul(v_size_x27_2249_, v___x_2252_);
v___x_2254_ = lean_unsigned_to_nat(3u);
v___x_2255_ = lean_nat_div(v___x_2253_, v___x_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_array_get_size(v_buckets_x27_2251_);
v___x_2257_ = lean_nat_dec_le(v___x_2255_, v___x_2256_);
lean_dec(v___x_2255_);
if (v___x_2257_ == 0)
{
lean_object* v_val_2258_; lean_object* v___x_2260_; 
v_val_2258_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2251_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v_val_2258_);
lean_ctor_set(v___x_2226_, 0, v_size_x27_2249_);
v___x_2260_ = v___x_2226_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_size_x27_2249_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_val_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
else
{
lean_object* v___x_2263_; 
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v_buckets_x27_2251_);
lean_ctor_set(v___x_2226_, 0, v_size_x27_2249_);
v___x_2263_ = v___x_2226_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_size_x27_2249_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_buckets_x27_2251_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v_buckets_x27_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
lean_inc(v_bkt_2246_);
v___x_2265_ = lean_box(0);
v_buckets_x27_2266_ = lean_array_uset(v_buckets_2224_, v___x_2245_, v___x_2265_);
v___x_2267_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2221_, v_b_2222_, v_bkt_2246_);
v___x_2268_ = lean_array_uset(v_buckets_x27_2266_, v___x_2245_, v___x_2267_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2268_);
v___x_2270_ = v___x_2226_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_size_2223_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2276_, lean_object* v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2277_) == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_box(0);
return v___x_2278_;
}
else
{
lean_object* v_key_2279_; lean_object* v_value_2280_; lean_object* v_tail_2281_; lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v_fst_2284_; lean_object* v_snd_2285_; uint8_t v___x_2290_; 
v_key_2279_ = lean_ctor_get(v_x_2277_, 0);
v_value_2280_ = lean_ctor_get(v_x_2277_, 1);
v_tail_2281_ = lean_ctor_get(v_x_2277_, 2);
v_fst_2282_ = lean_ctor_get(v_key_2279_, 0);
v_snd_2283_ = lean_ctor_get(v_key_2279_, 1);
v_fst_2284_ = lean_ctor_get(v_a_2276_, 0);
v_snd_2285_ = lean_ctor_get(v_a_2276_, 1);
v___x_2290_ = lean_unbox(v_fst_2282_);
if (v___x_2290_ == 0)
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_unbox(v_fst_2284_);
if (v___x_2291_ == 0)
{
goto v___jp_2286_;
}
else
{
v_x_2277_ = v_tail_2281_;
goto _start;
}
}
else
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_unbox(v_fst_2284_);
if (v___x_2293_ == 0)
{
v_x_2277_ = v_tail_2281_;
goto _start;
}
else
{
goto v___jp_2286_;
}
}
v___jp_2286_:
{
uint8_t v___x_2287_; 
v___x_2287_ = l_Lean_ExprStructEq_beq(v_snd_2283_, v_snd_2285_);
if (v___x_2287_ == 0)
{
v_x_2277_ = v_tail_2281_;
goto _start;
}
else
{
lean_object* v___x_2289_; 
lean_inc(v_value_2280_);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_value_2280_);
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2295_, lean_object* v_x_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2295_, v_x_2296_);
lean_dec(v_x_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_buckets_2300_; lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2303_; uint64_t v___y_2305_; uint8_t v___x_2321_; 
v_buckets_2300_ = lean_ctor_get(v_m_2298_, 1);
v_fst_2301_ = lean_ctor_get(v_a_2299_, 0);
v_snd_2302_ = lean_ctor_get(v_a_2299_, 1);
v___x_2303_ = lean_array_get_size(v_buckets_2300_);
v___x_2321_ = lean_unbox(v_fst_2301_);
if (v___x_2321_ == 0)
{
uint64_t v___x_2322_; 
v___x_2322_ = 13ULL;
v___y_2305_ = v___x_2322_;
goto v___jp_2304_;
}
else
{
uint64_t v___x_2323_; 
v___x_2323_ = 11ULL;
v___y_2305_ = v___x_2323_;
goto v___jp_2304_;
}
v___jp_2304_:
{
uint64_t v___x_2306_; uint64_t v___x_2307_; uint64_t v___x_2308_; uint64_t v___x_2309_; uint64_t v_fold_2310_; uint64_t v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; size_t v___x_2314_; size_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2306_ = l_Lean_ExprStructEq_hash(v_snd_2302_);
v___x_2307_ = lean_uint64_mix_hash(v___y_2305_, v___x_2306_);
v___x_2308_ = 32ULL;
v___x_2309_ = lean_uint64_shift_right(v___x_2307_, v___x_2308_);
v_fold_2310_ = lean_uint64_xor(v___x_2307_, v___x_2309_);
v___x_2311_ = 16ULL;
v___x_2312_ = lean_uint64_shift_right(v_fold_2310_, v___x_2311_);
v___x_2313_ = lean_uint64_xor(v_fold_2310_, v___x_2312_);
v___x_2314_ = lean_uint64_to_usize(v___x_2313_);
v___x_2315_ = lean_usize_of_nat(v___x_2303_);
v___x_2316_ = ((size_t)1ULL);
v___x_2317_ = lean_usize_sub(v___x_2315_, v___x_2316_);
v___x_2318_ = lean_usize_land(v___x_2314_, v___x_2317_);
v___x_2319_ = lean_array_uget_borrowed(v_buckets_2300_, v___x_2318_);
v___x_2320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2299_, v___x_2319_);
return v___x_2320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2324_, v_a_2325_);
lean_dec_ref(v_a_2325_);
lean_dec_ref(v_m_2324_);
return v_res_2326_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2327_; lean_object* v_dummy_2328_; 
v___x_2327_ = lean_box(0);
v_dummy_2328_ = l_Lean_Expr_sort___override(v___x_2327_);
return v_dummy_2328_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2329_, lean_object* v_fst_2330_, lean_object* v_fvars_2331_, lean_object* v_a_2332_, lean_object* v_b_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_a_2343_; uint8_t v___x_2347_; 
v___x_2347_ = lean_nat_dec_lt(v_a_2332_, v_upperBound_2329_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_a_2332_);
lean_dec(v_fvars_2331_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_b_2333_);
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v_binderInfo_2351_; uint8_t v___x_2352_; 
v___x_2349_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2350_ = lean_array_get_borrowed(v___x_2349_, v_fst_2330_, v_a_2332_);
v_binderInfo_2351_ = lean_ctor_get_uint8(v___x_2350_, sizeof(void*)*2);
v___x_2352_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2351_);
if (v___x_2352_ == 0)
{
v_a_2343_ = v_b_2333_;
goto v___jp_2342_;
}
else
{
uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2353_ = 0;
v___x_2354_ = l_Lean_instInhabitedExpr;
v___x_2355_ = lean_array_get_borrowed(v___x_2354_, v_b_2333_, v_a_2332_);
lean_inc(v___x_2355_);
lean_inc(v_fvars_2331_);
v___x_2356_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2331_, v___x_2355_, v___x_2353_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = lean_array_set(v_b_2333_, v_a_2332_, v_a_2357_);
v_a_2343_ = v___x_2358_;
goto v___jp_2342_;
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v_b_2333_);
lean_dec(v_a_2332_);
lean_dec(v_fvars_2331_);
v_a_2359_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2356_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2356_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
v___jp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = lean_nat_add(v_a_2332_, v___x_2344_);
lean_dec(v_a_2332_);
v_a_2332_ = v___x_2345_;
v_b_2333_ = v_a_2343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2367_, size_t v_sz_2368_, size_t v_i_2369_, lean_object* v_bs_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
uint8_t v___x_2379_; 
v___x_2379_ = lean_usize_dec_lt(v_i_2369_, v_sz_2368_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_dec(v_fvars_2367_);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v_bs_2370_);
return v___x_2380_;
}
else
{
uint8_t v___x_2381_; lean_object* v_v_2382_; lean_object* v___x_2383_; 
v___x_2381_ = 0;
v_v_2382_ = lean_array_uget_borrowed(v_bs_2370_, v_i_2369_);
lean_inc(v_v_2382_);
lean_inc(v_fvars_2367_);
v___x_2383_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2367_, v_v_2382_, v___x_2381_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; lean_object* v_bs_x27_2386_; size_t v___x_2387_; size_t v___x_2388_; lean_object* v___x_2389_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = lean_unsigned_to_nat(0u);
v_bs_x27_2386_ = lean_array_uset(v_bs_2370_, v_i_2369_, v___x_2385_);
v___x_2387_ = ((size_t)1ULL);
v___x_2388_ = lean_usize_add(v_i_2369_, v___x_2387_);
v___x_2389_ = lean_array_uset(v_bs_x27_2386_, v_i_2369_, v_a_2384_);
v_i_2369_ = v___x_2388_;
v_bs_2370_ = v___x_2389_;
goto _start;
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v_bs_2370_);
lean_dec(v_fvars_2367_);
v_a_2391_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2383_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2383_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2399_, lean_object* v_f_2400_, lean_object* v_args_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
uint8_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = 0;
lean_inc_ref(v_f_2400_);
lean_inc(v_fvars_2399_);
v___x_2411_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2399_, v_f_2400_, v___x_2410_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2411_) == 0)
{
uint8_t v_implicits_2412_; 
v_implicits_2412_ = lean_ctor_get_uint8(v_a_2402_, 2);
if (v_implicits_2412_ == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2411_);
lean_inc(v_a_2408_);
lean_inc_ref(v_a_2407_);
lean_inc(v_a_2406_);
lean_inc_ref(v_a_2405_);
v___x_2414_ = lean_infer_type(v_f_2400_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref(v___x_2414_);
v___x_2416_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2415_, v_args_2401_, v___x_2410_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v_fst_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2416_);
v_fst_2418_ = lean_ctor_get(v_a_2417_, 0);
lean_inc(v_fst_2418_);
lean_dec(v_a_2417_);
v___x_2419_ = lean_array_get_size(v_args_2401_);
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2419_, v_fst_2418_, v_fvars_2399_, v___x_2420_, v_args_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_fst_2418_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2430_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = l_Lean_mkAppN(v_a_2413_, v_a_2422_);
lean_dec(v_a_2422_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2426_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_a_2413_);
v_a_2431_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2421_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2421_);
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
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v_a_2413_);
lean_dec_ref(v_args_2401_);
lean_dec(v_fvars_2399_);
v_a_2439_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2416_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2416_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_dec(v_a_2413_);
lean_dec_ref(v_args_2401_);
lean_dec(v_fvars_2399_);
return v___x_2414_;
}
}
else
{
lean_object* v_a_2447_; size_t v_sz_2448_; size_t v___x_2449_; lean_object* v___x_2450_; 
lean_dec_ref(v_f_2400_);
v_a_2447_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2447_);
lean_dec_ref(v___x_2411_);
v_sz_2448_ = lean_array_size(v_args_2401_);
v___x_2449_ = ((size_t)0ULL);
v___x_2450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2399_, v_sz_2448_, v___x_2449_, v_args_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2459_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = l_Lean_mkAppN(v_a_2447_, v_a_2451_);
lean_dec(v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2457_ = v___x_2453_;
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
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_a_2447_);
v_a_2460_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2450_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2450_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2401_);
lean_dec_ref(v_f_2400_);
lean_dec(v_fvars_2399_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2468_, lean_object* v_f_2469_, lean_object* v_args_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2468_, v_f_2469_, v_args_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2480_, lean_object* v_b_2481_, uint8_t v___x_2482_, lean_object* v_mk_2483_, lean_object* v_a_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_inc_ref(v_x_2485_);
v___x_2494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2494_, 0, v_x_2485_);
lean_ctor_set(v___x_2494_, 1, v_fvars_2480_);
v___x_2495_ = lean_expr_instantiate1(v_b_2481_, v_x_2485_);
v___x_2496_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2494_, v___x_2495_, v___x_2482_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2496_) == 0)
{
uint8_t v_lift_2497_; 
v_lift_2497_ = lean_ctor_get_uint8(v___y_2486_, 10);
if (v_lift_2497_ == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2510_; 
v_a_2498_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2500_ = v___x_2496_;
v_isShared_2501_ = v_isSharedCheck_2510_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2496_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2510_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2503_ = lean_mk_empty_array_with_capacity(v___x_2502_);
v___x_2504_ = lean_array_push(v___x_2503_, v_x_2485_);
v___x_2505_ = lean_expr_abstract(v_a_2498_, v___x_2504_);
lean_dec_ref(v___x_2504_);
lean_dec(v_a_2498_);
v___x_2506_ = lean_apply_2(v_mk_2483_, v_a_2484_, v___x_2505_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2506_);
v___x_2508_ = v___x_2500_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_a_2511_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___x_2496_);
v___x_2512_ = l_Lean_Expr_fvarId_x21(v_x_2485_);
v___x_2513_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2512_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2527_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2527_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2527_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2518_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2514_, v_a_2511_);
lean_dec(v_a_2514_);
v___x_2519_ = lean_unsigned_to_nat(1u);
v___x_2520_ = lean_mk_empty_array_with_capacity(v___x_2519_);
v___x_2521_ = lean_array_push(v___x_2520_, v_x_2485_);
v___x_2522_ = lean_expr_abstract(v___x_2518_, v___x_2521_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v___x_2518_);
v___x_2523_ = lean_apply_2(v_mk_2483_, v_a_2484_, v___x_2522_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2523_);
v___x_2525_ = v___x_2516_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_a_2511_);
lean_dec_ref(v_x_2485_);
lean_dec_ref(v_a_2484_);
lean_dec_ref(v_mk_2483_);
v_a_2528_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2513_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2513_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2485_);
lean_dec_ref(v_a_2484_);
lean_dec_ref(v_mk_2483_);
return v___x_2496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2536_, lean_object* v_b_2537_, lean_object* v___x_2538_, lean_object* v_mk_2539_, lean_object* v_a_2540_, lean_object* v_x_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
uint8_t v___x_51510__boxed_2550_; lean_object* v_res_2551_; 
v___x_51510__boxed_2550_ = lean_unbox(v___x_2538_);
v_res_2551_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2536_, v_b_2537_, v___x_51510__boxed_2550_, v_mk_2539_, v_a_2540_, v_x_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v_b_2537_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2552_, lean_object* v_n_2553_, lean_object* v_t_2554_, lean_object* v_b_2555_, uint8_t v_i_2556_, lean_object* v_mk_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
uint8_t v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = 0;
lean_inc(v_fvars_2552_);
v___x_2567_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2552_, v_t_2554_, v___x_2566_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
if (lean_obj_tag(v___x_2567_) == 0)
{
uint8_t v_underBinder_2568_; 
v_underBinder_2568_ = lean_ctor_get_uint8(v_a_2558_, 4);
if (v_underBinder_2568_ == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_n_2553_);
lean_dec(v_fvars_2552_);
v_a_2569_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2571_ = v___x_2567_;
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2567_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_apply_2(v_mk_2557_, v_a_2569_, v_b_2555_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2573_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2579_; lean_object* v___f_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; 
v_a_2578_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_n(v_a_2578_, 2);
lean_dec_ref(v___x_2567_);
v___x_2579_ = lean_box(v___x_2566_);
v___f_2580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2580_, 0, v_fvars_2552_);
lean_closure_set(v___f_2580_, 1, v_b_2555_);
lean_closure_set(v___f_2580_, 2, v___x_2579_);
lean_closure_set(v___f_2580_, 3, v_mk_2557_);
lean_closure_set(v___f_2580_, 4, v_a_2578_);
v___x_2581_ = 0;
v___x_2582_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2553_, v_i_2556_, v_a_2578_, v___f_2580_, v___x_2581_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
return v___x_2582_;
}
}
else
{
lean_dec_ref(v_mk_2557_);
lean_dec_ref(v_b_2555_);
lean_dec(v_n_2553_);
lean_dec(v_fvars_2552_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2583_, lean_object* v_n_2584_, lean_object* v_t_2585_, lean_object* v_b_2586_, lean_object* v_i_2587_, lean_object* v_mk_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
uint8_t v_i_boxed_2597_; lean_object* v_res_2598_; 
v_i_boxed_2597_ = lean_unbox(v_i_2587_);
v_res_2598_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2583_, v_n_2584_, v_t_2585_, v_b_2586_, v_i_boxed_2597_, v_mk_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2599_, lean_object* v_e_2600_, lean_object* v_topLevel_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
uint8_t v_topLevel_boxed_2610_; lean_object* v_res_2611_; 
v_topLevel_boxed_2610_ = lean_unbox(v_topLevel_2601_);
v_res_2611_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2599_, v_e_2600_, v_topLevel_boxed_2610_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
return v_res_2611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2616_ = lean_unsigned_to_nat(27u);
v___x_2617_ = lean_unsigned_to_nat(1955u);
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2620_ = l_mkPanicMessageWithDecl(v___x_2619_, v___x_2618_, v___x_2617_, v___x_2616_, v___x_2615_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2621_, lean_object* v_fvars_2622_, lean_object* v_b_2623_, uint8_t v___x_2624_, lean_object* v_e_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, uint8_t v_isLet_2628_, uint8_t v_topLevel_2629_, lean_object* v_x_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
if (v_fst_2621_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_inc_ref(v_x_2630_);
v___x_2639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_x_2630_);
lean_ctor_set(v___x_2639_, 1, v_fvars_2622_);
v___x_2640_ = lean_expr_instantiate1(v_b_2623_, v_x_2630_);
v___x_2641_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2639_, v___x_2640_, v___x_2624_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2641_) == 0)
{
if (lean_obj_tag(v_e_2625_) == 8)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2677_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2677_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2677_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_declName_2646_; lean_object* v_type_2647_; lean_object* v_value_2648_; lean_object* v_body_2649_; uint8_t v_nondep_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___y_2656_; size_t v___x_2671_; size_t v___x_2672_; uint8_t v___x_2673_; 
v_declName_2646_ = lean_ctor_get(v_e_2625_, 0);
v_type_2647_ = lean_ctor_get(v_e_2625_, 1);
v_value_2648_ = lean_ctor_get(v_e_2625_, 2);
v_body_2649_ = lean_ctor_get(v_e_2625_, 3);
v_nondep_2650_ = lean_ctor_get_uint8(v_e_2625_, sizeof(void*)*4 + 8);
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_2652_ = lean_mk_empty_array_with_capacity(v___x_2651_);
v___x_2653_ = lean_array_push(v___x_2652_, v_x_2630_);
v___x_2654_ = lean_expr_abstract(v_a_2642_, v___x_2653_);
lean_dec_ref(v___x_2653_);
lean_dec(v_a_2642_);
v___x_2671_ = lean_ptr_addr(v_type_2647_);
v___x_2672_ = lean_ptr_addr(v_a_2626_);
v___x_2673_ = lean_usize_dec_eq(v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
v___y_2656_ = v___x_2673_;
goto v___jp_2655_;
}
else
{
size_t v___x_2674_; size_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2674_ = lean_ptr_addr(v_value_2648_);
v___x_2675_ = lean_ptr_addr(v_a_2627_);
v___x_2676_ = lean_usize_dec_eq(v___x_2674_, v___x_2675_);
v___y_2656_ = v___x_2676_;
goto v___jp_2655_;
}
v___jp_2655_:
{
if (v___y_2656_ == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
lean_inc(v_declName_2646_);
lean_dec_ref(v_e_2625_);
v___x_2657_ = l_Lean_Expr_letE___override(v_declName_2646_, v_a_2626_, v_a_2627_, v___x_2654_, v_nondep_2650_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2657_);
v___x_2659_ = v___x_2644_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
else
{
size_t v___x_2661_; size_t v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = lean_ptr_addr(v_body_2649_);
v___x_2662_ = lean_ptr_addr(v___x_2654_);
v___x_2663_ = lean_usize_dec_eq(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
lean_inc(v_declName_2646_);
lean_dec_ref(v_e_2625_);
v___x_2664_ = l_Lean_Expr_letE___override(v_declName_2646_, v_a_2626_, v_a_2627_, v___x_2654_, v_nondep_2650_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2664_);
v___x_2666_ = v___x_2644_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
else
{
lean_object* v___x_2669_; 
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_a_2627_);
lean_dec_ref(v_a_2626_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_e_2625_);
v___x_2669_ = v___x_2644_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_e_2625_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
else
{
lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v_x_2630_);
lean_dec_ref(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec_ref(v_e_2625_);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2641_, 0);
lean_dec(v_unused_2687_);
v___x_2679_ = v___x_2641_;
v_isShared_2680_ = v_isSharedCheck_2686_;
goto v_resetjp_2678_;
}
else
{
lean_dec(v___x_2641_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2686_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2682_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2681_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v___x_2682_);
v___x_2684_ = v___x_2679_;
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
}
}
else
{
lean_dec_ref(v_x_2630_);
lean_dec_ref(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec_ref(v_e_2625_);
return v___x_2641_;
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_dec_ref(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec_ref(v_e_2625_);
v___x_2688_ = l_Lean_Expr_fvarId_x21(v_x_2630_);
v___x_2689_ = l_Lean_FVarId_getDecl___redArg(v___x_2688_, v___y_2634_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref(v___x_2689_);
v___x_2691_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2690_, v_isLet_2628_, v___y_2631_, v___y_2633_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec_ref(v___x_2691_);
v___x_2692_ = lean_expr_instantiate1(v_b_2623_, v_x_2630_);
lean_dec_ref(v_x_2630_);
v___x_2693_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2622_, v___x_2692_, v_topLevel_2629_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2693_;
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_x_2630_);
lean_dec(v_fvars_2622_);
v_a_2694_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2691_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2691_);
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
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_x_2630_);
lean_dec(v_fvars_2622_);
v_a_2702_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2689_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2689_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2710_ = _args[0];
lean_object* v_fvars_2711_ = _args[1];
lean_object* v_b_2712_ = _args[2];
lean_object* v___x_2713_ = _args[3];
lean_object* v_e_2714_ = _args[4];
lean_object* v_a_2715_ = _args[5];
lean_object* v_a_2716_ = _args[6];
lean_object* v_isLet_2717_ = _args[7];
lean_object* v_topLevel_2718_ = _args[8];
lean_object* v_x_2719_ = _args[9];
lean_object* v___y_2720_ = _args[10];
lean_object* v___y_2721_ = _args[11];
lean_object* v___y_2722_ = _args[12];
lean_object* v___y_2723_ = _args[13];
lean_object* v___y_2724_ = _args[14];
lean_object* v___y_2725_ = _args[15];
lean_object* v___y_2726_ = _args[16];
lean_object* v___y_2727_ = _args[17];
_start:
{
uint8_t v_fst_51655__boxed_2728_; uint8_t v___x_51656__boxed_2729_; uint8_t v_isLet_boxed_2730_; uint8_t v_topLevel_boxed_2731_; lean_object* v_res_2732_; 
v_fst_51655__boxed_2728_ = lean_unbox(v_fst_2710_);
v___x_51656__boxed_2729_ = lean_unbox(v___x_2713_);
v_isLet_boxed_2730_ = lean_unbox(v_isLet_2717_);
v_topLevel_boxed_2731_ = lean_unbox(v_topLevel_2718_);
v_res_2732_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_51655__boxed_2728_, v_fvars_2711_, v_b_2712_, v___x_51656__boxed_2729_, v_e_2714_, v_a_2715_, v_a_2716_, v_isLet_boxed_2730_, v_topLevel_boxed_2731_, v_x_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec_ref(v_b_2712_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2733_, lean_object* v_e_2734_, uint8_t v_isLet_2735_, lean_object* v_n_2736_, lean_object* v_t_2737_, lean_object* v_v_2738_, lean_object* v_b_2739_, uint8_t v_topLevel_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; uint8_t v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = 0;
lean_inc(v_fvars_2733_);
v___x_2764_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2733_, v_t_2737_, v___x_2763_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2883_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2883_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2883_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; 
lean_inc(v_fvars_2733_);
v___x_2769_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2733_, v_v_2738_, v___x_2763_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2882_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2882_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2882_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
uint8_t v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; uint8_t v___y_2778_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; uint8_t v_descend_2822_; uint8_t v_underBinder_2823_; uint8_t v_usedOnly_2824_; uint8_t v_merge_2825_; uint8_t v_lift_2826_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; uint8_t v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; uint8_t v___y_2864_; 
v_descend_2822_ = lean_ctor_get_uint8(v_a_2741_, 3);
v_underBinder_2823_ = lean_ctor_get_uint8(v_a_2741_, 4);
v_usedOnly_2824_ = lean_ctor_get_uint8(v_a_2741_, 5);
v_merge_2825_ = lean_ctor_get_uint8(v_a_2741_, 6);
v_lift_2826_ = lean_ctor_get_uint8(v_a_2741_, 10);
if (v_usedOnly_2824_ == 0)
{
v___y_2864_ = v___x_2763_;
goto v___jp_2863_;
}
else
{
uint8_t v___x_2880_; 
v___x_2880_ = l_Lean_Expr_hasLooseBVars(v_b_2739_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; 
lean_del_object(v___x_2772_);
lean_dec(v_a_2770_);
lean_del_object(v___x_2767_);
lean_dec(v_a_2765_);
lean_dec(v_n_2736_);
lean_dec_ref(v_e_2734_);
v___x_2881_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2733_, v_b_2739_, v_topLevel_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
return v___x_2881_;
}
else
{
v___y_2864_ = v___x_2763_;
goto v___jp_2863_;
}
}
v___jp_2774_:
{
if (v___y_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_dec_ref(v___y_2777_);
lean_dec_ref(v_e_2734_);
v___x_2779_ = l_Lean_Expr_letE___override(v___y_2776_, v_a_2765_, v_a_2770_, v_b_2739_, v___y_2775_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2779_);
v___x_2781_ = v___x_2772_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
else
{
size_t v___x_2783_; size_t v___x_2784_; uint8_t v___x_2785_; 
v___x_2783_ = lean_ptr_addr(v___y_2777_);
lean_dec_ref(v___y_2777_);
v___x_2784_ = lean_ptr_addr(v_b_2739_);
v___x_2785_ = lean_usize_dec_eq(v___x_2783_, v___x_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_dec_ref(v_e_2734_);
v___x_2786_ = l_Lean_Expr_letE___override(v___y_2776_, v_a_2765_, v_a_2770_, v_b_2739_, v___y_2775_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2786_);
v___x_2788_ = v___x_2772_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
else
{
lean_object* v___x_2791_; 
lean_dec(v___y_2776_);
lean_dec(v_a_2770_);
lean_dec(v_a_2765_);
lean_dec_ref(v_b_2739_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v_e_2734_);
v___x_2791_ = v___x_2772_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_e_2734_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
v___jp_2793_:
{
if (lean_obj_tag(v_e_2734_) == 8)
{
lean_object* v_declName_2794_; lean_object* v_type_2795_; lean_object* v_value_2796_; lean_object* v_body_2797_; uint8_t v_nondep_2798_; size_t v___x_2799_; size_t v___x_2800_; uint8_t v___x_2801_; 
lean_del_object(v___x_2767_);
v_declName_2794_ = lean_ctor_get(v_e_2734_, 0);
v_type_2795_ = lean_ctor_get(v_e_2734_, 1);
v_value_2796_ = lean_ctor_get(v_e_2734_, 2);
v_body_2797_ = lean_ctor_get(v_e_2734_, 3);
v_nondep_2798_ = lean_ctor_get_uint8(v_e_2734_, sizeof(void*)*4 + 8);
v___x_2799_ = lean_ptr_addr(v_type_2795_);
v___x_2800_ = lean_ptr_addr(v_a_2765_);
v___x_2801_ = lean_usize_dec_eq(v___x_2799_, v___x_2800_);
if (v___x_2801_ == 0)
{
lean_inc_ref(v_body_2797_);
lean_inc(v_declName_2794_);
v___y_2775_ = v_nondep_2798_;
v___y_2776_ = v_declName_2794_;
v___y_2777_ = v_body_2797_;
v___y_2778_ = v___x_2801_;
goto v___jp_2774_;
}
else
{
size_t v___x_2802_; size_t v___x_2803_; uint8_t v___x_2804_; 
v___x_2802_ = lean_ptr_addr(v_value_2796_);
v___x_2803_ = lean_ptr_addr(v_a_2770_);
v___x_2804_ = lean_usize_dec_eq(v___x_2802_, v___x_2803_);
lean_inc_ref(v_body_2797_);
lean_inc(v_declName_2794_);
v___y_2775_ = v_nondep_2798_;
v___y_2776_ = v_declName_2794_;
v___y_2777_ = v_body_2797_;
v___y_2778_ = v___x_2804_;
goto v___jp_2774_;
}
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_del_object(v___x_2772_);
lean_dec(v_a_2770_);
lean_dec(v_a_2765_);
lean_dec_ref(v_b_2739_);
lean_dec_ref(v_e_2734_);
v___x_2805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2806_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2805_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2806_);
v___x_2808_ = v___x_2767_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
v___jp_2810_:
{
uint8_t v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = 0;
v___x_2821_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2813_, v_a_2765_, v_a_2770_, v___y_2818_, v___x_2763_, v___x_2820_, v___y_2812_, v___y_2814_, v___y_2811_, v___y_2816_, v___y_2819_, v___y_2815_, v___y_2817_);
return v___x_2821_;
}
v___jp_2827_:
{
if (v_underBinder_2823_ == 0)
{
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2830_);
goto v___jp_2793_;
}
else
{
if (v_descend_2822_ == 0)
{
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2830_);
goto v___jp_2793_;
}
else
{
lean_del_object(v___x_2772_);
lean_del_object(v___x_2767_);
lean_dec_ref(v_b_2739_);
lean_dec_ref(v_e_2734_);
v___y_2811_ = v___y_2828_;
v___y_2812_ = v___y_2829_;
v___y_2813_ = v___y_2830_;
v___y_2814_ = v___y_2831_;
v___y_2815_ = v___y_2833_;
v___y_2816_ = v___y_2832_;
v___y_2817_ = v___y_2834_;
v___y_2818_ = v___y_2835_;
v___y_2819_ = v___y_2836_;
goto v___jp_2810_;
}
}
}
v___jp_2837_:
{
lean_object* v___x_2846_; 
lean_inc(v_a_2770_);
lean_inc(v_a_2765_);
v___x_2846_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2733_, v_n_2736_, v_a_2765_, v_a_2770_, v___y_2839_, v___y_2841_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___f_2853_; uint8_t v___x_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___x_2846_);
v_fst_2848_ = lean_ctor_get(v_a_2847_, 0);
lean_inc_n(v_fst_2848_, 2);
v_snd_2849_ = lean_ctor_get(v_a_2847_, 1);
lean_inc(v_snd_2849_);
lean_dec(v_a_2847_);
v___x_2850_ = lean_box(v___x_2763_);
v___x_2851_ = lean_box(v_isLet_2735_);
v___x_2852_ = lean_box(v_topLevel_2740_);
lean_inc(v_a_2770_);
lean_inc(v_a_2765_);
lean_inc_ref(v_e_2734_);
lean_inc_ref(v_b_2739_);
v___f_2853_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2853_, 0, v_fst_2848_);
lean_closure_set(v___f_2853_, 1, v_fvars_2733_);
lean_closure_set(v___f_2853_, 2, v_b_2739_);
lean_closure_set(v___f_2853_, 3, v___x_2850_);
lean_closure_set(v___f_2853_, 4, v_e_2734_);
lean_closure_set(v___f_2853_, 5, v_a_2765_);
lean_closure_set(v___f_2853_, 6, v_a_2770_);
lean_closure_set(v___f_2853_, 7, v___x_2851_);
lean_closure_set(v___f_2853_, 8, v___x_2852_);
v___x_2854_ = lean_unbox(v_fst_2848_);
lean_dec(v_fst_2848_);
if (v___x_2854_ == 0)
{
v___y_2828_ = v___y_2841_;
v___y_2829_ = v___y_2839_;
v___y_2830_ = v_snd_2849_;
v___y_2831_ = v___y_2840_;
v___y_2832_ = v___y_2842_;
v___y_2833_ = v___y_2844_;
v___y_2834_ = v___y_2845_;
v___y_2835_ = v___f_2853_;
v___y_2836_ = v___y_2843_;
goto v___jp_2827_;
}
else
{
if (v___y_2838_ == 0)
{
lean_del_object(v___x_2772_);
lean_del_object(v___x_2767_);
lean_dec_ref(v_b_2739_);
lean_dec_ref(v_e_2734_);
v___y_2811_ = v___y_2841_;
v___y_2812_ = v___y_2839_;
v___y_2813_ = v_snd_2849_;
v___y_2814_ = v___y_2840_;
v___y_2815_ = v___y_2844_;
v___y_2816_ = v___y_2842_;
v___y_2817_ = v___y_2845_;
v___y_2818_ = v___f_2853_;
v___y_2819_ = v___y_2843_;
goto v___jp_2810_;
}
else
{
v___y_2828_ = v___y_2841_;
v___y_2829_ = v___y_2839_;
v___y_2830_ = v_snd_2849_;
v___y_2831_ = v___y_2840_;
v___y_2832_ = v___y_2842_;
v___y_2833_ = v___y_2844_;
v___y_2834_ = v___y_2845_;
v___y_2835_ = v___f_2853_;
v___y_2836_ = v___y_2843_;
goto v___jp_2827_;
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_del_object(v___x_2772_);
lean_dec(v_a_2770_);
lean_del_object(v___x_2767_);
lean_dec(v_a_2765_);
lean_dec_ref(v_b_2739_);
lean_dec_ref(v_e_2734_);
lean_dec(v_fvars_2733_);
v_a_2855_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2846_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2846_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
v___jp_2863_:
{
if (v_merge_2825_ == 0)
{
v___y_2838_ = v___y_2864_;
v___y_2839_ = v_a_2741_;
v___y_2840_ = v_a_2742_;
v___y_2841_ = v_a_2743_;
v___y_2842_ = v_a_2744_;
v___y_2843_ = v_a_2745_;
v___y_2844_ = v_a_2746_;
v___y_2845_ = v_a_2747_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2865_; lean_object* v_valueMap_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_st_ref_get(v_a_2743_);
v_valueMap_2866_ = lean_ctor_get(v___x_2865_, 2);
lean_inc_ref(v_valueMap_2866_);
lean_dec(v___x_2865_);
v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2866_, v_a_2770_);
lean_dec_ref(v_valueMap_2866_);
if (lean_obj_tag(v___x_2867_) == 1)
{
lean_del_object(v___x_2772_);
lean_dec(v_a_2770_);
lean_del_object(v___x_2767_);
lean_dec(v_a_2765_);
lean_dec(v_n_2736_);
lean_dec_ref(v_e_2734_);
if (v_isLet_2735_ == 0)
{
lean_object* v_val_2868_; 
v_val_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref(v___x_2867_);
v___y_2750_ = v_val_2868_;
v___y_2751_ = v_a_2741_;
v___y_2752_ = v_a_2742_;
v___y_2753_ = v_a_2743_;
v___y_2754_ = v_a_2744_;
v___y_2755_ = v_a_2745_;
v___y_2756_ = v_a_2746_;
v___y_2757_ = v_a_2747_;
goto v___jp_2749_;
}
else
{
if (v_lift_2826_ == 0)
{
lean_object* v_val_2869_; 
v_val_2869_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_val_2869_);
lean_dec_ref(v___x_2867_);
v___y_2750_ = v_val_2869_;
v___y_2751_ = v_a_2741_;
v___y_2752_ = v_a_2742_;
v___y_2753_ = v_a_2743_;
v___y_2754_ = v_a_2744_;
v___y_2755_ = v_a_2745_;
v___y_2756_ = v_a_2746_;
v___y_2757_ = v_a_2747_;
goto v___jp_2749_;
}
else
{
lean_object* v_val_2870_; lean_object* v___x_2871_; 
v_val_2870_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_val_2870_);
lean_dec_ref(v___x_2867_);
v___x_2871_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2870_, v_a_2743_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_dec_ref(v___x_2871_);
v___y_2750_ = v_val_2870_;
v___y_2751_ = v_a_2741_;
v___y_2752_ = v_a_2742_;
v___y_2753_ = v_a_2743_;
v___y_2754_ = v_a_2744_;
v___y_2755_ = v_a_2745_;
v___y_2756_ = v_a_2746_;
v___y_2757_ = v_a_2747_;
goto v___jp_2749_;
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_val_2870_);
lean_dec_ref(v_b_2739_);
lean_dec(v_fvars_2733_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2867_);
v___y_2838_ = v___y_2864_;
v___y_2839_ = v_a_2741_;
v___y_2840_ = v_a_2742_;
v___y_2841_ = v_a_2743_;
v___y_2842_ = v_a_2744_;
v___y_2843_ = v_a_2745_;
v___y_2844_ = v_a_2746_;
v___y_2845_ = v_a_2747_;
goto v___jp_2837_;
}
}
}
}
}
else
{
lean_del_object(v___x_2767_);
lean_dec(v_a_2765_);
lean_dec_ref(v_b_2739_);
lean_dec(v_n_2736_);
lean_dec_ref(v_e_2734_);
lean_dec(v_fvars_2733_);
return v___x_2769_;
}
}
}
else
{
lean_dec_ref(v_b_2739_);
lean_dec_ref(v_v_2738_);
lean_dec(v_n_2736_);
lean_dec_ref(v_e_2734_);
lean_dec(v_fvars_2733_);
return v___x_2764_;
}
v___jp_2749_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_inc(v___y_2750_);
v___x_2758_ = l_Lean_Expr_fvar___override(v___y_2750_);
v___x_2759_ = lean_expr_instantiate1(v_b_2739_, v___x_2758_);
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_b_2739_);
v___x_2760_ = lean_box(v_topLevel_2740_);
v___x_2761_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2761_, 0, v_fvars_2733_);
lean_closure_set(v___x_2761_, 1, v___x_2759_);
lean_closure_set(v___x_2761_, 2, v___x_2760_);
v___x_2762_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2750_, v___x_2761_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2750_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2884_, lean_object* v_struct_2885_, lean_object* v___y_2886_, lean_object* v_typeName_2887_, lean_object* v_idx_2888_, lean_object* v_e_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
uint8_t v___y_51431__boxed_2898_; lean_object* v_res_2899_; 
v___y_51431__boxed_2898_ = lean_unbox(v___y_2886_);
v_res_2899_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2884_, v_struct_2885_, v___y_51431__boxed_2898_, v_typeName_2887_, v_idx_2888_, v_e_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2899_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2903_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2904_ = lean_unsigned_to_nat(75u);
v___x_2905_ = lean_unsigned_to_nat(229u);
v___x_2906_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2907_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2908_ = l_mkPanicMessageWithDecl(v___x_2907_, v___x_2906_, v___x_2905_, v___x_2904_, v___x_2903_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2909_, lean_object* v_e_2910_, lean_object* v_fvars_2911_, uint8_t v___x_2912_, uint8_t v_topLevel_2913_, uint8_t v___y_2914_, lean_object* v_____r_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_k_2925_; 
switch(lean_obj_tag(v_e_2910_))
{
case 5:
{
lean_object* v___x_2928_; lean_object* v_dummy_2929_; lean_object* v_nargs_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2928_ = l_Lean_Expr_getAppFn(v_e_2910_);
v_dummy_2929_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2930_ = l_Lean_Expr_getAppNumArgs(v_e_2910_);
lean_inc(v_nargs_2930_);
v___x_2931_ = lean_mk_array(v_nargs_2930_, v_dummy_2929_);
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_nat_sub(v_nargs_2930_, v___x_2932_);
lean_dec(v_nargs_2930_);
lean_inc_ref(v_e_2910_);
v___x_2934_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2910_, v___x_2931_, v___x_2933_);
v___x_2935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2935_, 0, v_fvars_2911_);
lean_closure_set(v___x_2935_, 1, v___x_2928_);
lean_closure_set(v___x_2935_, 2, v___x_2934_);
v_k_2925_ = v___x_2935_;
goto v___jp_2924_;
}
case 6:
{
lean_object* v_binderName_2936_; lean_object* v_binderType_2937_; lean_object* v_body_2938_; uint8_t v_binderInfo_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_binderName_2936_ = lean_ctor_get(v_e_2910_, 0);
v_binderType_2937_ = lean_ctor_get(v_e_2910_, 1);
v_body_2938_ = lean_ctor_get(v_e_2910_, 2);
v_binderInfo_2939_ = lean_ctor_get_uint8(v_e_2910_, sizeof(void*)*3 + 8);
v___x_2940_ = lean_box(v_binderInfo_2939_);
lean_inc_ref_n(v_body_2938_, 2);
lean_inc_ref_n(v_binderType_2937_, 2);
lean_inc_ref(v_e_2910_);
lean_inc_n(v_binderName_2936_, 2);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2941_, 0, v_binderName_2936_);
lean_closure_set(v___f_2941_, 1, v___x_2940_);
lean_closure_set(v___f_2941_, 2, v_e_2910_);
lean_closure_set(v___f_2941_, 3, v_binderType_2937_);
lean_closure_set(v___f_2941_, 4, v_body_2938_);
v___x_2942_ = lean_box(v_binderInfo_2939_);
v___x_2943_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2943_, 0, v_fvars_2911_);
lean_closure_set(v___x_2943_, 1, v_binderName_2936_);
lean_closure_set(v___x_2943_, 2, v_binderType_2937_);
lean_closure_set(v___x_2943_, 3, v_body_2938_);
lean_closure_set(v___x_2943_, 4, v___x_2942_);
lean_closure_set(v___x_2943_, 5, v___f_2941_);
v_k_2925_ = v___x_2943_;
goto v___jp_2924_;
}
case 7:
{
lean_object* v_binderName_2944_; lean_object* v_binderType_2945_; lean_object* v_body_2946_; uint8_t v_binderInfo_2947_; lean_object* v___x_2948_; lean_object* v___f_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_binderName_2944_ = lean_ctor_get(v_e_2910_, 0);
v_binderType_2945_ = lean_ctor_get(v_e_2910_, 1);
v_body_2946_ = lean_ctor_get(v_e_2910_, 2);
v_binderInfo_2947_ = lean_ctor_get_uint8(v_e_2910_, sizeof(void*)*3 + 8);
v___x_2948_ = lean_box(v_binderInfo_2947_);
lean_inc_ref_n(v_body_2946_, 2);
lean_inc_ref_n(v_binderType_2945_, 2);
lean_inc_ref(v_e_2910_);
lean_inc_n(v_binderName_2944_, 2);
v___f_2949_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2949_, 0, v_binderName_2944_);
lean_closure_set(v___f_2949_, 1, v___x_2948_);
lean_closure_set(v___f_2949_, 2, v_e_2910_);
lean_closure_set(v___f_2949_, 3, v_binderType_2945_);
lean_closure_set(v___f_2949_, 4, v_body_2946_);
v___x_2950_ = lean_box(v_binderInfo_2947_);
v___x_2951_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2951_, 0, v_fvars_2911_);
lean_closure_set(v___x_2951_, 1, v_binderName_2944_);
lean_closure_set(v___x_2951_, 2, v_binderType_2945_);
lean_closure_set(v___x_2951_, 3, v_body_2946_);
lean_closure_set(v___x_2951_, 4, v___x_2950_);
lean_closure_set(v___x_2951_, 5, v___f_2949_);
v_k_2925_ = v___x_2951_;
goto v___jp_2924_;
}
case 8:
{
uint8_t v_nondep_2952_; 
v_nondep_2952_ = lean_ctor_get_uint8(v_e_2910_, sizeof(void*)*4 + 8);
if (v_nondep_2952_ == 0)
{
lean_object* v_declName_2953_; lean_object* v_type_2954_; lean_object* v_value_2955_; lean_object* v_body_2956_; lean_object* v___x_2957_; 
v_declName_2953_ = lean_ctor_get(v_e_2910_, 0);
lean_inc(v_declName_2953_);
v_type_2954_ = lean_ctor_get(v_e_2910_, 1);
lean_inc_ref(v_type_2954_);
v_value_2955_ = lean_ctor_get(v_e_2910_, 2);
lean_inc_ref(v_value_2955_);
v_body_2956_ = lean_ctor_get(v_e_2910_, 3);
lean_inc_ref(v_body_2956_);
v___x_2957_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2911_, v_e_2910_, v___x_2912_, v_declName_2953_, v_type_2954_, v_value_2955_, v_body_2956_, v_topLevel_2913_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2957_;
}
else
{
lean_object* v_declName_2958_; lean_object* v_type_2959_; lean_object* v_value_2960_; lean_object* v_body_2961_; lean_object* v___x_2962_; 
v_declName_2958_ = lean_ctor_get(v_e_2910_, 0);
lean_inc(v_declName_2958_);
v_type_2959_ = lean_ctor_get(v_e_2910_, 1);
lean_inc_ref(v_type_2959_);
v_value_2960_ = lean_ctor_get(v_e_2910_, 2);
lean_inc_ref(v_value_2960_);
v_body_2961_ = lean_ctor_get(v_e_2910_, 3);
lean_inc_ref(v_body_2961_);
v___x_2962_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2911_, v_e_2910_, v___y_2914_, v_declName_2958_, v_type_2959_, v_value_2960_, v_body_2961_, v_topLevel_2913_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2962_;
}
}
case 10:
{
lean_object* v_data_2963_; lean_object* v_expr_2964_; lean_object* v___x_2965_; 
v_data_2963_ = lean_ctor_get(v_e_2910_, 0);
v_expr_2964_ = lean_ctor_get(v_e_2910_, 1);
lean_inc_ref(v_expr_2964_);
v___x_2965_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2911_, v_expr_2964_, v_topLevel_2913_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2980_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2980_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2980_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
size_t v___x_2970_; size_t v___x_2971_; uint8_t v___x_2972_; 
v___x_2970_ = lean_ptr_addr(v_expr_2964_);
v___x_2971_ = lean_ptr_addr(v_a_2966_);
v___x_2972_ = lean_usize_dec_eq(v___x_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_inc(v_data_2963_);
lean_dec_ref(v_e_2910_);
v___x_2973_ = l_Lean_Expr_mdata___override(v_data_2963_, v_a_2966_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2973_);
v___x_2975_ = v___x_2968_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
else
{
lean_object* v___x_2978_; 
lean_dec(v_a_2966_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v_e_2910_);
v___x_2978_ = v___x_2968_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_e_2910_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_dec_ref(v_e_2910_);
return v___x_2965_;
}
}
case 11:
{
lean_object* v_typeName_2981_; lean_object* v_idx_2982_; lean_object* v_struct_2983_; lean_object* v___x_2984_; lean_object* v___f_2985_; 
v_typeName_2981_ = lean_ctor_get(v_e_2910_, 0);
v_idx_2982_ = lean_ctor_get(v_e_2910_, 1);
v_struct_2983_ = lean_ctor_get(v_e_2910_, 2);
v___x_2984_ = lean_box(v___y_2914_);
lean_inc_ref(v_e_2910_);
lean_inc(v_idx_2982_);
lean_inc(v_typeName_2981_);
lean_inc_ref(v_struct_2983_);
v___f_2985_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2985_, 0, v_fvars_2911_);
lean_closure_set(v___f_2985_, 1, v_struct_2983_);
lean_closure_set(v___f_2985_, 2, v___x_2984_);
lean_closure_set(v___f_2985_, 3, v_typeName_2981_);
lean_closure_set(v___f_2985_, 4, v_idx_2982_);
lean_closure_set(v___f_2985_, 5, v_e_2910_);
v_k_2925_ = v___f_2985_;
goto v___jp_2924_;
}
default: 
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v_fvars_2911_);
lean_dec_ref(v_e_2910_);
v___x_2986_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2987_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2986_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2987_;
}
}
v___jp_2924_:
{
if (v_descend_2909_ == 0)
{
lean_object* v___x_2926_; 
lean_dec_ref(v_k_2925_);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_e_2910_);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; 
lean_dec_ref(v_e_2910_);
lean_inc(v___y_2922_);
lean_inc_ref(v___y_2921_);
lean_inc(v___y_2920_);
lean_inc_ref(v___y_2919_);
lean_inc(v___y_2918_);
lean_inc(v___y_2917_);
lean_inc_ref(v___y_2916_);
v___x_2927_ = lean_apply_8(v_k_2925_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, lean_box(0));
return v___x_2927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2988_, lean_object* v_e_2989_, lean_object* v_fvars_2990_, lean_object* v___x_2991_, lean_object* v_topLevel_2992_, lean_object* v___y_2993_, lean_object* v_____r_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
uint8_t v_descend_boxed_3003_; uint8_t v___x_51584__boxed_3004_; uint8_t v_topLevel_boxed_3005_; uint8_t v___y_51585__boxed_3006_; lean_object* v_res_3007_; 
v_descend_boxed_3003_ = lean_unbox(v_descend_2988_);
v___x_51584__boxed_3004_ = lean_unbox(v___x_2991_);
v_topLevel_boxed_3005_ = lean_unbox(v_topLevel_2992_);
v___y_51585__boxed_3006_ = lean_unbox(v___y_2993_);
v_res_3007_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_3003_, v_e_2989_, v_fvars_2990_, v___x_51584__boxed_3004_, v_topLevel_boxed_3005_, v___y_51585__boxed_3006_, v_____r_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_3008_, lean_object* v_e_3009_, uint8_t v_topLevel_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v___y_3020_; lean_object* v_a_3021_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___x_3035_; 
v___x_3035_ = l_Lean_Expr_isAtomic(v_e_3009_);
if (v___x_3035_ == 0)
{
uint8_t v_proofs_3036_; uint8_t v_types_3037_; uint8_t v_descend_3038_; lean_object* v___y_3040_; lean_object* v___y_3041_; uint8_t v___y_3058_; 
v_proofs_3036_ = lean_ctor_get_uint8(v_a_3011_, 0);
v_types_3037_ = lean_ctor_get_uint8(v_a_3011_, 1);
v_descend_3038_ = lean_ctor_get_uint8(v_a_3011_, 3);
if (v_descend_3038_ == 0)
{
goto v___jp_3081_;
}
else
{
if (v___x_3035_ == 0)
{
v___y_3058_ = v___x_3035_;
goto v___jp_3057_;
}
else
{
goto v___jp_3081_;
}
}
v___jp_3039_:
{
if (v_proofs_3036_ == 0)
{
lean_object* v___x_3042_; 
lean_inc_ref(v_e_3009_);
v___x_3042_ = l_Lean_Meta_isProof(v_e_3009_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; uint8_t v___x_3044_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = lean_unbox(v_a_3043_);
lean_dec(v_a_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v_e_3009_);
v___x_3045_ = lean_box(0);
lean_inc(v_a_3017_);
lean_inc_ref(v_a_3016_);
lean_inc(v_a_3015_);
lean_inc_ref(v_a_3014_);
lean_inc(v_a_3013_);
lean_inc(v_a_3012_);
lean_inc_ref(v_a_3011_);
v___x_3046_ = lean_apply_9(v___y_3040_, v___x_3045_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, lean_box(0));
v___y_3027_ = v___y_3041_;
v___y_3028_ = v___x_3046_;
goto v___jp_3026_;
}
else
{
lean_dec_ref(v___y_3040_);
v___y_3020_ = v___y_3041_;
v_a_3021_ = v_e_3009_;
goto v___jp_3019_;
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec_ref(v_e_3009_);
v_a_3047_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3042_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3042_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref(v_e_3009_);
v___x_3055_ = lean_box(0);
lean_inc(v_a_3017_);
lean_inc_ref(v_a_3016_);
lean_inc(v_a_3015_);
lean_inc_ref(v_a_3014_);
lean_inc(v_a_3013_);
lean_inc(v_a_3012_);
lean_inc_ref(v_a_3011_);
v___x_3056_ = lean_apply_9(v___y_3040_, v___x_3055_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, lean_box(0));
v___y_3027_ = v___y_3041_;
v___y_3028_ = v___x_3056_;
goto v___jp_3026_;
}
}
v___jp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3059_ = lean_st_ref_get(v_a_3012_);
v___x_3060_ = lean_box(v_topLevel_3010_);
lean_inc_ref(v_e_3009_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
lean_ctor_set(v___x_3061_, 1, v_e_3009_);
v___x_3062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3059_, v___x_3061_);
lean_dec(v___x_3059_);
if (lean_obj_tag(v___x_3062_) == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_Meta_ExtractLets_containsLet(v_e_3009_);
if (v___x_3063_ == 0)
{
lean_dec(v_fvars_3008_);
v___y_3020_ = v___x_3061_;
v_a_3021_ = v_e_3009_;
goto v___jp_3019_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___f_3068_; lean_object* v___x_3069_; lean_object* v___f_3070_; 
v___x_3064_ = lean_box(v_descend_3038_);
v___x_3065_ = lean_box(v___x_3063_);
v___x_3066_ = lean_box(v_topLevel_3010_);
v___x_3067_ = lean_box(v___y_3058_);
lean_inc_ref_n(v_e_3009_, 2);
v___f_3068_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3068_, 0, v___x_3064_);
lean_closure_set(v___f_3068_, 1, v_e_3009_);
lean_closure_set(v___f_3068_, 2, v_fvars_3008_);
lean_closure_set(v___f_3068_, 3, v___x_3065_);
lean_closure_set(v___f_3068_, 4, v___x_3066_);
lean_closure_set(v___f_3068_, 5, v___x_3067_);
v___x_3069_ = lean_box(v_types_3037_);
lean_inc_ref(v___f_3068_);
v___f_3070_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3070_, 0, v___x_3069_);
lean_closure_set(v___f_3070_, 1, v_e_3009_);
lean_closure_set(v___f_3070_, 2, v___f_3068_);
if (v_topLevel_3010_ == 0)
{
lean_dec_ref(v___f_3068_);
v___y_3040_ = v___f_3070_;
v___y_3041_ = v___x_3061_;
goto v___jp_3039_;
}
else
{
uint8_t v___x_3071_; 
v___x_3071_ = l_Lean_Expr_isLet(v_e_3009_);
if (v___x_3071_ == 0)
{
uint8_t v___x_3072_; 
v___x_3072_ = l_Lean_Expr_isMData(v_e_3009_);
if (v___x_3072_ == 0)
{
lean_dec_ref(v___f_3068_);
v___y_3040_ = v___f_3070_;
v___y_3041_ = v___x_3061_;
goto v___jp_3039_;
}
else
{
lean_dec_ref(v___f_3070_);
lean_dec_ref(v_e_3009_);
v___y_3031_ = v___f_3068_;
v___y_3032_ = v___x_3061_;
goto v___jp_3030_;
}
}
else
{
lean_dec_ref(v___f_3070_);
lean_dec_ref(v_e_3009_);
v___y_3031_ = v___f_3068_;
v___y_3032_ = v___x_3061_;
goto v___jp_3030_;
}
}
}
}
else
{
lean_object* v_val_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v___x_3061_);
lean_dec_ref(v_e_3009_);
lean_dec(v_fvars_3008_);
v_val_3073_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3062_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_val_3073_);
lean_dec(v___x_3062_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
lean_ctor_set_tag(v___x_3075_, 0);
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_val_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
v___jp_3081_:
{
if (v_topLevel_3010_ == 0)
{
lean_object* v___x_3082_; 
lean_dec(v_fvars_3008_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v_e_3009_);
return v___x_3082_;
}
else
{
if (v___x_3035_ == 0)
{
v___y_3058_ = v___x_3035_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3083_; 
lean_dec(v_fvars_3008_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v_e_3009_);
return v___x_3083_;
}
}
}
}
else
{
lean_object* v___x_3084_; 
lean_dec(v_fvars_3008_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v_e_3009_);
return v___x_3084_;
}
v___jp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = lean_st_ref_take(v_a_3012_);
lean_inc_ref(v_a_3021_);
v___x_3023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3022_, v___y_3020_, v_a_3021_);
v___x_3024_ = lean_st_ref_set(v_a_3012_, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_a_3021_);
return v___x_3025_;
}
v___jp_3026_:
{
if (lean_obj_tag(v___y_3028_) == 0)
{
lean_object* v_a_3029_; 
v_a_3029_ = lean_ctor_get(v___y_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___y_3028_);
v___y_3020_ = v___y_3027_;
v_a_3021_ = v_a_3029_;
goto v___jp_3019_;
}
else
{
lean_dec_ref(v___y_3027_);
return v___y_3028_;
}
}
v___jp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_box(0);
lean_inc(v_a_3017_);
lean_inc_ref(v_a_3016_);
lean_inc(v_a_3015_);
lean_inc_ref(v_a_3014_);
lean_inc(v_a_3013_);
lean_inc(v_a_3012_);
lean_inc_ref(v_a_3011_);
v___x_3034_ = lean_apply_9(v___y_3031_, v___x_3033_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, lean_box(0));
v___y_3027_ = v___y_3032_;
v___y_3028_ = v___x_3034_;
goto v___jp_3026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3085_, lean_object* v_struct_3086_, uint8_t v___y_3087_, lean_object* v_typeName_3088_, lean_object* v_idx_3089_, lean_object* v_e_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; 
lean_inc_ref(v_struct_3086_);
v___x_3099_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3085_, v_struct_3086_, v___y_3087_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3114_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3114_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3114_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
size_t v___x_3104_; size_t v___x_3105_; uint8_t v___x_3106_; 
v___x_3104_ = lean_ptr_addr(v_struct_3086_);
lean_dec_ref(v_struct_3086_);
v___x_3105_ = lean_ptr_addr(v_a_3100_);
v___x_3106_ = lean_usize_dec_eq(v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
lean_dec_ref(v_e_3090_);
v___x_3107_ = l_Lean_Expr_proj___override(v_typeName_3088_, v_idx_3089_, v_a_3100_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3107_);
v___x_3109_ = v___x_3102_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
lean_object* v___x_3112_; 
lean_dec(v_a_3100_);
lean_dec(v_idx_3089_);
lean_dec(v_typeName_3088_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v_e_3090_);
v___x_3112_ = v___x_3102_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_e_3090_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_dec_ref(v_e_3090_);
lean_dec(v_idx_3089_);
lean_dec(v_typeName_3088_);
lean_dec_ref(v_struct_3086_);
return v___x_3099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3115_, lean_object* v_sz_3116_, lean_object* v_i_3117_, lean_object* v_bs_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
size_t v_sz_boxed_3127_; size_t v_i_boxed_3128_; lean_object* v_res_3129_; 
v_sz_boxed_3127_ = lean_unbox_usize(v_sz_3116_);
lean_dec(v_sz_3116_);
v_i_boxed_3128_ = lean_unbox_usize(v_i_3117_);
lean_dec(v_i_3117_);
v_res_3129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3115_, v_sz_boxed_3127_, v_i_boxed_3128_, v_bs_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3130_, lean_object* v_fst_3131_, lean_object* v_fvars_3132_, lean_object* v_a_3133_, lean_object* v_b_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3130_, v_fst_3131_, v_fvars_3132_, v_a_3133_, v_b_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v_fst_3131_);
lean_dec(v_upperBound_3130_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3144_, lean_object* v_e_3145_, lean_object* v_isLet_3146_, lean_object* v_n_3147_, lean_object* v_t_3148_, lean_object* v_v_3149_, lean_object* v_b_3150_, lean_object* v_topLevel_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
uint8_t v_isLet_boxed_3160_; uint8_t v_topLevel_boxed_3161_; lean_object* v_res_3162_; 
v_isLet_boxed_3160_ = lean_unbox(v_isLet_3146_);
v_topLevel_boxed_3161_ = lean_unbox(v_topLevel_3151_);
v_res_3162_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3144_, v_e_3145_, v_isLet_boxed_3160_, v_n_3147_, v_t_3148_, v_v_3149_, v_b_3150_, v_topLevel_boxed_3161_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3163_, lean_object* v_name_3164_, lean_object* v_type_3165_, lean_object* v_val_3166_, lean_object* v_k_3167_, uint8_t v_nondep_3168_, uint8_t v_kind_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3164_, v_type_3165_, v_val_3166_, v_k_3167_, v_nondep_3168_, v_kind_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_name_3180_, lean_object* v_type_3181_, lean_object* v_val_3182_, lean_object* v_k_3183_, lean_object* v_nondep_3184_, lean_object* v_kind_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_nondep_boxed_3194_; uint8_t v_kind_boxed_3195_; lean_object* v_res_3196_; 
v_nondep_boxed_3194_ = lean_unbox(v_nondep_3184_);
v_kind_boxed_3195_ = lean_unbox(v_kind_3185_);
v_res_3196_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3179_, v_name_3180_, v_type_3181_, v_val_3182_, v_k_3183_, v_nondep_boxed_3194_, v_kind_boxed_3195_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3197_, lean_object* v_m_3198_, lean_object* v_a_3199_, lean_object* v_b_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3198_, v_a_3199_, v_b_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3202_, lean_object* v_m_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3203_, v_a_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3206_, lean_object* v_m_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3206_, v_m_3207_, v_a_3208_);
lean_dec_ref(v_a_3208_);
lean_dec_ref(v_m_3207_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3210_, lean_object* v_fst_3211_, lean_object* v_fvars_3212_, lean_object* v_inst_3213_, lean_object* v_R_3214_, lean_object* v_a_3215_, lean_object* v_b_3216_, lean_object* v_c_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3210_, v_fst_3211_, v_fvars_3212_, v_a_3215_, v_b_3216_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3227_, lean_object* v_fst_3228_, lean_object* v_fvars_3229_, lean_object* v_inst_3230_, lean_object* v_R_3231_, lean_object* v_a_3232_, lean_object* v_b_3233_, lean_object* v_c_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3227_, v_fst_3228_, v_fvars_3229_, v_inst_3230_, v_R_3231_, v_a_3232_, v_b_3233_, v_c_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v_fst_3228_);
lean_dec(v_upperBound_3227_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3244_, lean_object* v_m_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3245_, v_a_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3248_, lean_object* v_m_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3248_, v_m_3249_, v_a_3250_);
lean_dec_ref(v_a_3250_);
lean_dec_ref(v_m_3249_);
return v_res_3251_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3252_, lean_object* v_a_3253_, lean_object* v_x_3254_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3253_, v_x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3256_, lean_object* v_a_3257_, lean_object* v_x_3258_){
_start:
{
uint8_t v_res_3259_; lean_object* v_r_3260_; 
v_res_3259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3256_, v_a_3257_, v_x_3258_);
lean_dec(v_x_3258_);
lean_dec_ref(v_a_3257_);
v_r_3260_ = lean_box(v_res_3259_);
return v_r_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3261_, lean_object* v_data_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3264_, lean_object* v_a_3265_, lean_object* v_b_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3265_, v_b_3266_, v_x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3269_, lean_object* v_a_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3270_, v_x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3273_, lean_object* v_a_3274_, lean_object* v_x_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3273_, v_a_3274_, v_x_3275_);
lean_dec(v_x_3275_);
lean_dec_ref(v_a_3274_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3277_, lean_object* v_a_3278_, lean_object* v_x_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3278_, v_x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3281_, lean_object* v_a_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3281_, v_a_3282_, v_x_3283_);
lean_dec(v_x_3283_);
lean_dec_ref(v_a_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3285_, lean_object* v_i_3286_, lean_object* v_source_3287_, lean_object* v_target_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3286_, v_source_3287_, v_target_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3290_, lean_object* v_x_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3291_, v_x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v___x_3303_; lean_object* v_a_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; 
v___x_3303_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3294_, v_a_3299_);
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = lean_box(0);
v___x_3306_ = 1;
v___x_3307_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3305_, v_a_3304_, v___x_3306_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3318_, size_t v_i_3319_, lean_object* v_bs_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_usize_dec_lt(v_i_3319_, v_sz_3318_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_bs_3320_);
return v___x_3330_;
}
else
{
lean_object* v_v_3331_; lean_object* v___x_3332_; 
v_v_3331_ = lean_array_uget_borrowed(v_bs_3320_, v_i_3319_);
lean_inc(v_v_3331_);
v___x_3332_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3331_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; lean_object* v_bs_x27_3335_; size_t v___x_3336_; size_t v___x_3337_; lean_object* v___x_3338_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = lean_unsigned_to_nat(0u);
v_bs_x27_3335_ = lean_array_uset(v_bs_3320_, v_i_3319_, v___x_3334_);
v___x_3336_ = ((size_t)1ULL);
v___x_3337_ = lean_usize_add(v_i_3319_, v___x_3336_);
v___x_3338_ = lean_array_uset(v_bs_x27_3335_, v_i_3319_, v_a_3333_);
v_i_3319_ = v___x_3337_;
v_bs_3320_ = v___x_3338_;
goto _start;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref(v_bs_3320_);
v_a_3340_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3332_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3332_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3348_, lean_object* v_i_3349_, lean_object* v_bs_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
size_t v_sz_boxed_3359_; size_t v_i_boxed_3360_; lean_object* v_res_3361_; 
v_sz_boxed_3359_ = lean_unbox_usize(v_sz_3348_);
lean_dec(v_sz_3348_);
v_i_boxed_3360_ = lean_unbox_usize(v_i_3349_);
lean_dec(v_i_3349_);
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3359_, v_i_boxed_3360_, v_bs_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v_merge_3382_; 
v_merge_3382_ = lean_ctor_get_uint8(v_a_3363_, 6);
if (v_merge_3382_ == 0)
{
v___y_3372_ = v_a_3363_;
v___y_3373_ = v_a_3364_;
v___y_3374_ = v_a_3365_;
v___y_3375_ = v_a_3366_;
v___y_3376_ = v_a_3367_;
v___y_3377_ = v_a_3368_;
v___y_3378_ = v_a_3369_;
goto v___jp_3371_;
}
else
{
uint8_t v_useContext_3383_; 
v_useContext_3383_ = lean_ctor_get_uint8(v_a_3363_, 7);
if (v_useContext_3383_ == 0)
{
v___y_3372_ = v_a_3363_;
v___y_3373_ = v_a_3364_;
v___y_3374_ = v_a_3365_;
v___y_3375_ = v_a_3366_;
v___y_3376_ = v_a_3367_;
v___y_3377_ = v_a_3368_;
v___y_3378_ = v_a_3369_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3384_; 
v___x_3384_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_dec_ref(v___x_3384_);
v___y_3372_ = v_a_3363_;
v___y_3373_ = v_a_3364_;
v___y_3374_ = v_a_3365_;
v___y_3375_ = v_a_3366_;
v___y_3376_ = v_a_3367_;
v___y_3377_ = v_a_3368_;
v___y_3378_ = v_a_3369_;
goto v___jp_3371_;
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v_es_3362_);
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
v___jp_3371_:
{
size_t v_sz_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v_sz_3379_ = lean_array_size(v_es_3362_);
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3379_, v___x_3380_, v_es_3362_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Meta_ExtractLets_extract(v_es_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3403_, lean_object* v_x_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3403_, v_x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
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
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3410_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3410_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3427_, lean_object* v_x_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3427_, v_x_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3435_, lean_object* v_decls_3436_, lean_object* v_x_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3436_, v_x_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3444_, lean_object* v_decls_3445_, lean_object* v_x_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3444_, v_decls_3445_, v_x_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3453_, size_t v_i_3454_, lean_object* v_bs_3455_){
_start:
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_usize_dec_lt(v_i_3454_, v_sz_3453_);
if (v___x_3456_ == 0)
{
return v_bs_3455_;
}
else
{
lean_object* v_v_3457_; lean_object* v___x_3458_; lean_object* v_bs_x27_3459_; lean_object* v___x_3460_; size_t v___x_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
v_v_3457_ = lean_array_uget(v_bs_3455_, v_i_3454_);
v___x_3458_ = lean_unsigned_to_nat(0u);
v_bs_x27_3459_ = lean_array_uset(v_bs_3455_, v_i_3454_, v___x_3458_);
v___x_3460_ = l_Lean_LocalDecl_fvarId(v_v_3457_);
lean_dec(v_v_3457_);
v___x_3461_ = ((size_t)1ULL);
v___x_3462_ = lean_usize_add(v_i_3454_, v___x_3461_);
v___x_3463_ = lean_array_uset(v_bs_x27_3459_, v_i_3454_, v___x_3460_);
v_i_3454_ = v___x_3462_;
v_bs_3455_ = v___x_3463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3465_, lean_object* v_i_3466_, lean_object* v_bs_3467_){
_start:
{
size_t v_sz_boxed_3468_; size_t v_i_boxed_3469_; lean_object* v_res_3470_; 
v_sz_boxed_3468_ = lean_unbox_usize(v_sz_3465_);
lean_dec(v_sz_3465_);
v_i_boxed_3469_ = lean_unbox_usize(v_i_3466_);
lean_dec(v_i_3466_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3468_, v_i_boxed_3469_, v_bs_3467_);
return v_res_3470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(0);
v___x_3472_ = lean_unsigned_to_nat(16u);
v___x_3473_ = lean_mk_array(v___x_3472_, v___x_3471_);
return v___x_3473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3475_ = lean_unsigned_to_nat(0u);
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
lean_ctor_set(v___x_3476_, 1, v___x_3474_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3477_, lean_object* v_givenNames_3478_, lean_object* v_k_3479_, lean_object* v_config_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3487_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3488_, 0, v_givenNames_3478_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
lean_ctor_set(v___x_3488_, 2, v___x_3486_);
v___x_3489_ = lean_st_mk_ref(v___x_3488_);
v___x_3490_ = lean_st_mk_ref(v___x_3486_);
v___x_3491_ = l_Lean_Meta_ExtractLets_extract(v_es_3477_, v_config_3480_, v___x_3490_, v___x_3489_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v_givenNames_3495_; lean_object* v_decls_3496_; size_t v_sz_3497_; size_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; size_t v_sz_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = lean_st_ref_get(v___x_3490_);
lean_dec(v___x_3490_);
lean_dec(v___x_3493_);
v___x_3494_ = lean_st_ref_get(v___x_3489_);
lean_dec(v___x_3489_);
v_givenNames_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_givenNames_3495_);
v_decls_3496_ = lean_ctor_get(v___x_3494_, 1);
lean_inc_ref(v_decls_3496_);
lean_dec(v___x_3494_);
v_sz_3497_ = lean_array_size(v_decls_3496_);
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_3497_, v___x_3498_, v_decls_3496_);
lean_inc_ref(v___x_3499_);
v___x_3500_ = lean_array_to_list(v___x_3499_);
v_sz_3501_ = lean_array_size(v___x_3499_);
v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3501_, v___x_3498_, v___x_3499_);
v___x_3503_ = lean_apply_3(v_k_3479_, v___x_3502_, v_a_3492_, v_givenNames_3495_);
v___x_3504_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3500_, v___x_3503_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
return v___x_3504_;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v___x_3490_);
lean_dec(v___x_3489_);
lean_dec_ref(v_k_3479_);
v_a_3505_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3491_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3491_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3513_, lean_object* v_givenNames_3514_, lean_object* v_k_3515_, lean_object* v_config_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3513_, v_givenNames_3514_, v_k_3515_, v_config_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec_ref(v_config_3516_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3523_, lean_object* v_es_3524_, lean_object* v_givenNames_3525_, lean_object* v_k_3526_, lean_object* v_config_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3524_, v_givenNames_3525_, v_k_3526_, v_config_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3534_, lean_object* v_es_3535_, lean_object* v_givenNames_3536_, lean_object* v_k_3537_, lean_object* v_config_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3534_, v_es_3535_, v_givenNames_3536_, v_k_3537_, v_config_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec_ref(v_config_3538_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3545_, lean_object* v_runInBase_3546_, lean_object* v_b_3547_, lean_object* v_c_3548_, lean_object* v_d_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_apply_3(v_k_3545_, v_b_3547_, v_c_3548_, v_d_3549_);
lean_inc(v___y_3553_);
lean_inc_ref(v___y_3552_);
lean_inc(v___y_3551_);
lean_inc_ref(v___y_3550_);
v___x_3556_ = lean_apply_7(v_runInBase_3546_, lean_box(0), v___x_3555_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, lean_box(0));
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3557_, lean_object* v_runInBase_3558_, lean_object* v_b_3559_, lean_object* v_c_3560_, lean_object* v_d_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3557_, v_runInBase_3558_, v_b_3559_, v_c_3560_, v_d_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3568_, lean_object* v_es_3569_, lean_object* v_givenNames_3570_, lean_object* v_config_3571_, lean_object* v_runInBase_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___f_3578_; lean_object* v___x_3579_; 
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3578_, 0, v_k_3568_);
lean_closure_set(v___f_3578_, 1, v_runInBase_3572_);
v___x_3579_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3569_, v_givenNames_3570_, v___f_3578_, v_config_3571_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3580_, lean_object* v_es_3581_, lean_object* v_givenNames_3582_, lean_object* v_config_3583_, lean_object* v_runInBase_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3580_, v_es_3581_, v_givenNames_3582_, v_config_3583_, v_runInBase_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec_ref(v_config_3583_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_es_3593_, lean_object* v_givenNames_3594_, lean_object* v_k_3595_, lean_object* v_config_3596_){
_start:
{
lean_object* v_toBind_3597_; lean_object* v_liftWith_3598_; lean_object* v_restoreM_3599_; lean_object* v___f_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_toBind_3597_ = lean_ctor_get(v_inst_3591_, 1);
lean_inc(v_toBind_3597_);
lean_dec_ref(v_inst_3591_);
v_liftWith_3598_ = lean_ctor_get(v_inst_3592_, 0);
lean_inc(v_liftWith_3598_);
v_restoreM_3599_ = lean_ctor_get(v_inst_3592_, 1);
lean_inc(v_restoreM_3599_);
lean_dec_ref(v_inst_3592_);
v___f_3600_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3600_, 0, v_k_3595_);
lean_closure_set(v___f_3600_, 1, v_es_3593_);
lean_closure_set(v___f_3600_, 2, v_givenNames_3594_);
lean_closure_set(v___f_3600_, 3, v_config_3596_);
v___x_3601_ = lean_apply_2(v_liftWith_3598_, lean_box(0), v___f_3600_);
v___x_3602_ = lean_apply_1(v_restoreM_3599_, lean_box(0));
v___x_3603_ = lean_apply_4(v_toBind_3597_, lean_box(0), lean_box(0), v___x_3601_, v___x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3604_, lean_object* v_00_u03b1_3605_, lean_object* v_inst_3606_, lean_object* v_inst_3607_, lean_object* v_es_3608_, lean_object* v_givenNames_3609_, lean_object* v_k_3610_, lean_object* v_config_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_Meta_extractLets___redArg(v_inst_3606_, v_inst_3607_, v_es_3608_, v_givenNames_3609_, v_k_3610_, v_config_3611_);
return v___x_3612_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3614_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3615_ = lean_box(0);
v___x_3616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v___x_3614_);
lean_ctor_set(v___x_3616_, 2, v___x_3613_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3617_, lean_object* v_config_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v_proofs_3629_; uint8_t v_types_3630_; uint8_t v_implicits_3631_; uint8_t v_descend_3632_; uint8_t v_underBinder_3633_; uint8_t v_usedOnly_3634_; uint8_t v_merge_3635_; uint8_t v_useContext_3636_; uint8_t v_preserveBinderNames_3637_; uint8_t v_lift_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3672_; 
v___x_3624_ = lean_unsigned_to_nat(0u);
v___x_3625_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3626_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3627_ = lean_st_mk_ref(v___x_3626_);
v___x_3628_ = lean_st_mk_ref(v___x_3625_);
v_proofs_3629_ = lean_ctor_get_uint8(v_config_3618_, 0);
v_types_3630_ = lean_ctor_get_uint8(v_config_3618_, 1);
v_implicits_3631_ = lean_ctor_get_uint8(v_config_3618_, 2);
v_descend_3632_ = lean_ctor_get_uint8(v_config_3618_, 3);
v_underBinder_3633_ = lean_ctor_get_uint8(v_config_3618_, 4);
v_usedOnly_3634_ = lean_ctor_get_uint8(v_config_3618_, 5);
v_merge_3635_ = lean_ctor_get_uint8(v_config_3618_, 6);
v_useContext_3636_ = lean_ctor_get_uint8(v_config_3618_, 7);
v_preserveBinderNames_3637_ = lean_ctor_get_uint8(v_config_3618_, 9);
v_lift_3638_ = lean_ctor_get_uint8(v_config_3618_, 10);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_config_3618_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3640_ = v_config_3618_;
v_isShared_3641_ = v_isSharedCheck_3672_;
goto v_resetjp_3639_;
}
else
{
lean_dec(v_config_3618_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3672_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; lean_object* v___x_3647_; 
v___x_3642_ = lean_unsigned_to_nat(1u);
v___x_3643_ = lean_mk_empty_array_with_capacity(v___x_3642_);
v___x_3644_ = lean_array_push(v___x_3643_, v_e_3617_);
v___x_3645_ = 1;
if (v_isShared_3641_ == 0)
{
v___x_3647_ = v___x_3640_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 0, v_proofs_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 1, v_types_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 2, v_implicits_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 3, v_descend_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 4, v_underBinder_3633_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 5, v_usedOnly_3634_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 6, v_merge_3635_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 7, v_useContext_3636_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 9, v_preserveBinderNames_3637_);
lean_ctor_set_uint8(v_reuseFailAlloc_3671_, 10, v_lift_3638_);
v___x_3647_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; 
lean_ctor_set_uint8(v___x_3647_, 8, v___x_3645_);
v___x_3648_ = l_Lean_Meta_ExtractLets_extract(v___x_3644_, v___x_3647_, v___x_3628_, v___x_3627_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_);
lean_dec_ref(v___x_3647_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3662_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3662_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3662_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v_decls_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3653_ = lean_st_ref_get(v___x_3628_);
lean_dec(v___x_3628_);
lean_dec(v___x_3653_);
v___x_3654_ = lean_st_ref_get(v___x_3627_);
lean_dec(v___x_3627_);
v_decls_3655_ = lean_ctor_get(v___x_3654_, 1);
lean_inc_ref(v_decls_3655_);
lean_dec(v___x_3654_);
v___x_3656_ = l_Lean_instInhabitedExpr;
v___x_3657_ = lean_array_get(v___x_3656_, v_a_3649_, v___x_3624_);
lean_dec(v_a_3649_);
v___x_3658_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3655_, v___x_3657_);
lean_dec_ref(v_decls_3655_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3658_);
v___x_3660_ = v___x_3651_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v___x_3628_);
lean_dec(v___x_3627_);
v_a_3663_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3648_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3648_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3673_, lean_object* v_config_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Meta_liftLets(v_e_3673_, v_config_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
return v_res_3680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3683_ = l_Lean_stringToMessageData(v___x_3682_);
return v___x_3683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3686_, lean_object* v_mvarId_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3694_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3686_, v_mvarId_3687_, v___x_3693_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3695_, lean_object* v_mvarId_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3695_, v_mvarId_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3703_, lean_object* v_tactic_3704_, lean_object* v_mvarId_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3704_, v_mvarId_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3712_, lean_object* v_tactic_3713_, lean_object* v_mvarId_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3712_, v_tactic_3713_, v_mvarId_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3721_, lean_object* v_b_3722_, lean_object* v_c_3723_, lean_object* v_d_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
lean_inc(v___y_3728_);
lean_inc_ref(v___y_3727_);
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
v___x_3730_ = lean_apply_8(v_k_3721_, v_b_3722_, v_c_3723_, v_d_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, lean_box(0));
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3731_, lean_object* v_b_3732_, lean_object* v_c_3733_, lean_object* v_d_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3731_, v_b_3732_, v_c_3733_, v_d_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3741_, lean_object* v_givenNames_3742_, lean_object* v_k_3743_, lean_object* v_config_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___f_3750_; lean_object* v___x_3751_; 
v___f_3750_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3750_, 0, v_k_3743_);
v___x_3751_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3741_, v_givenNames_3742_, v___f_3750_, v_config_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
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
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_a_3760_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3751_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3751_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3768_, lean_object* v_givenNames_3769_, lean_object* v_k_3770_, lean_object* v_config_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3768_, v_givenNames_3769_, v_k_3770_, v_config_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec_ref(v_config_3771_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3778_, lean_object* v_es_3779_, lean_object* v_givenNames_3780_, lean_object* v_k_3781_, lean_object* v_config_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3779_, v_givenNames_3780_, v_k_3781_, v_config_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3789_, lean_object* v_es_3790_, lean_object* v_givenNames_3791_, lean_object* v_k_3792_, lean_object* v_config_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3789_, v_es_3790_, v_givenNames_3791_, v_k_3792_, v_config_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_config_3793_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3800_, v_x_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
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
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_a_3816_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3807_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3807_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3824_, lean_object* v_x_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3824_, v_x_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3832_, lean_object* v_mvarId_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3833_, v_x_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3841_, lean_object* v_mvarId_3842_, lean_object* v_x_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3841_, v_mvarId_3842_, v_x_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3850_, lean_object* v_x_3851_, lean_object* v_x_3852_, lean_object* v_x_3853_){
_start:
{
lean_object* v_ks_3854_; lean_object* v_vs_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3879_; 
v_ks_3854_ = lean_ctor_get(v_x_3850_, 0);
v_vs_3855_ = lean_ctor_get(v_x_3850_, 1);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_x_3850_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3857_ = v_x_3850_;
v_isShared_3858_ = v_isSharedCheck_3879_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_vs_3855_);
lean_inc(v_ks_3854_);
lean_dec(v_x_3850_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3879_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3859_ = lean_array_get_size(v_ks_3854_);
v___x_3860_ = lean_nat_dec_lt(v_x_3851_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
lean_dec(v_x_3851_);
v___x_3861_ = lean_array_push(v_ks_3854_, v_x_3852_);
v___x_3862_ = lean_array_push(v_vs_3855_, v_x_3853_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___x_3862_);
lean_ctor_set(v___x_3857_, 0, v___x_3861_);
v___x_3864_ = v___x_3857_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
else
{
lean_object* v_k_x27_3866_; uint8_t v___x_3867_; 
v_k_x27_3866_ = lean_array_fget_borrowed(v_ks_3854_, v_x_3851_);
v___x_3867_ = l_Lean_instBEqMVarId_beq(v_x_3852_, v_k_x27_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3869_; 
if (v_isShared_3858_ == 0)
{
v___x_3869_ = v___x_3857_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_ks_3854_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_vs_3855_);
v___x_3869_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_unsigned_to_nat(1u);
v___x_3871_ = lean_nat_add(v_x_3851_, v___x_3870_);
lean_dec(v_x_3851_);
v_x_3850_ = v___x_3869_;
v_x_3851_ = v___x_3871_;
goto _start;
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v___x_3874_ = lean_array_fset(v_ks_3854_, v_x_3851_, v_x_3852_);
v___x_3875_ = lean_array_fset(v_vs_3855_, v_x_3851_, v_x_3853_);
lean_dec(v_x_3851_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___x_3875_);
lean_ctor_set(v___x_3857_, 0, v___x_3874_);
v___x_3877_ = v___x_3857_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3880_, lean_object* v_k_3881_, lean_object* v_v_3882_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3880_, v___x_3883_, v_k_3881_, v_v_3882_);
return v___x_3884_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_3885_; size_t v___x_3886_; size_t v___x_3887_; 
v___x_3885_ = ((size_t)5ULL);
v___x_3886_ = ((size_t)1ULL);
v___x_3887_ = lean_usize_shift_left(v___x_3886_, v___x_3885_);
return v___x_3887_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3888_; size_t v___x_3889_; size_t v___x_3890_; 
v___x_3888_ = ((size_t)1ULL);
v___x_3889_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3890_ = lean_usize_sub(v___x_3889_, v___x_3888_);
return v___x_3890_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3892_, size_t v_x_3893_, size_t v_x_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
if (lean_obj_tag(v_x_3892_) == 0)
{
lean_object* v_es_3897_; size_t v___x_3898_; size_t v___x_3899_; size_t v___x_3900_; size_t v___x_3901_; lean_object* v_j_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v_es_3897_ = lean_ctor_get(v_x_3892_, 0);
v___x_3898_ = ((size_t)5ULL);
v___x_3899_ = ((size_t)1ULL);
v___x_3900_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1);
v___x_3901_ = lean_usize_land(v_x_3893_, v___x_3900_);
v_j_3902_ = lean_usize_to_nat(v___x_3901_);
v___x_3903_ = lean_array_get_size(v_es_3897_);
v___x_3904_ = lean_nat_dec_lt(v_j_3902_, v___x_3903_);
if (v___x_3904_ == 0)
{
lean_dec(v_j_3902_);
lean_dec(v_x_3896_);
lean_dec(v_x_3895_);
return v_x_3892_;
}
else
{
lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3941_; 
lean_inc_ref(v_es_3897_);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_x_3892_);
if (v_isSharedCheck_3941_ == 0)
{
lean_object* v_unused_3942_; 
v_unused_3942_ = lean_ctor_get(v_x_3892_, 0);
lean_dec(v_unused_3942_);
v___x_3906_ = v_x_3892_;
v_isShared_3907_ = v_isSharedCheck_3941_;
goto v_resetjp_3905_;
}
else
{
lean_dec(v_x_3892_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3941_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v_v_3908_; lean_object* v___x_3909_; lean_object* v_xs_x27_3910_; lean_object* v___y_3912_; 
v_v_3908_ = lean_array_fget(v_es_3897_, v_j_3902_);
v___x_3909_ = lean_box(0);
v_xs_x27_3910_ = lean_array_fset(v_es_3897_, v_j_3902_, v___x_3909_);
switch(lean_obj_tag(v_v_3908_))
{
case 0:
{
lean_object* v_key_3917_; lean_object* v_val_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3928_; 
v_key_3917_ = lean_ctor_get(v_v_3908_, 0);
v_val_3918_ = lean_ctor_get(v_v_3908_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_v_3908_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3920_ = v_v_3908_;
v_isShared_3921_ = v_isSharedCheck_3928_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_val_3918_);
lean_inc(v_key_3917_);
lean_dec(v_v_3908_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3928_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
uint8_t v___x_3922_; 
v___x_3922_ = l_Lean_instBEqMVarId_beq(v_x_3895_, v_key_3917_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_del_object(v___x_3920_);
v___x_3923_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3917_, v_val_3918_, v_x_3895_, v_x_3896_);
v___x_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
v___y_3912_ = v___x_3924_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3926_; 
lean_dec(v_val_3918_);
lean_dec(v_key_3917_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 1, v_x_3896_);
lean_ctor_set(v___x_3920_, 0, v_x_3895_);
v___x_3926_ = v___x_3920_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_x_3895_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_x_3896_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
v___y_3912_ = v___x_3926_;
goto v___jp_3911_;
}
}
}
}
case 1:
{
lean_object* v_node_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3939_; 
v_node_3929_ = lean_ctor_get(v_v_3908_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_v_3908_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3931_ = v_v_3908_;
v_isShared_3932_ = v_isSharedCheck_3939_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_node_3929_);
lean_dec(v_v_3908_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3939_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
size_t v___x_3933_; size_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3933_ = lean_usize_shift_right(v_x_3893_, v___x_3898_);
v___x_3934_ = lean_usize_add(v_x_3894_, v___x_3899_);
v___x_3935_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3929_, v___x_3933_, v___x_3934_, v_x_3895_, v_x_3896_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3935_);
v___x_3937_ = v___x_3931_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
v___y_3912_ = v___x_3937_;
goto v___jp_3911_;
}
}
}
default: 
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3940_, 0, v_x_3895_);
lean_ctor_set(v___x_3940_, 1, v_x_3896_);
v___y_3912_ = v___x_3940_;
goto v___jp_3911_;
}
}
v___jp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
v___x_3913_ = lean_array_fset(v_xs_x27_3910_, v_j_3902_, v___y_3912_);
lean_dec(v_j_3902_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3913_);
v___x_3915_ = v___x_3906_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
}
else
{
lean_object* v_ks_3943_; lean_object* v_vs_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3964_; 
v_ks_3943_ = lean_ctor_get(v_x_3892_, 0);
v_vs_3944_ = lean_ctor_get(v_x_3892_, 1);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_x_3892_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3946_ = v_x_3892_;
v_isShared_3947_ = v_isSharedCheck_3964_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_vs_3944_);
lean_inc(v_ks_3943_);
lean_dec(v_x_3892_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3964_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_ks_3943_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_vs_3944_);
v___x_3949_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v_newNode_3950_; uint8_t v___y_3952_; size_t v___x_3958_; uint8_t v___x_3959_; 
v_newNode_3950_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3949_, v_x_3895_, v_x_3896_);
v___x_3958_ = ((size_t)7ULL);
v___x_3959_ = lean_usize_dec_le(v___x_3958_, v_x_3894_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3960_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3950_);
v___x_3961_ = lean_unsigned_to_nat(4u);
v___x_3962_ = lean_nat_dec_lt(v___x_3960_, v___x_3961_);
lean_dec(v___x_3960_);
v___y_3952_ = v___x_3962_;
goto v___jp_3951_;
}
else
{
v___y_3952_ = v___x_3959_;
goto v___jp_3951_;
}
v___jp_3951_:
{
if (v___y_3952_ == 0)
{
lean_object* v_ks_3953_; lean_object* v_vs_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_ks_3953_ = lean_ctor_get(v_newNode_3950_, 0);
lean_inc_ref(v_ks_3953_);
v_vs_3954_ = lean_ctor_get(v_newNode_3950_, 1);
lean_inc_ref(v_vs_3954_);
lean_dec_ref(v_newNode_3950_);
v___x_3955_ = lean_unsigned_to_nat(0u);
v___x_3956_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_3957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3894_, v_ks_3953_, v_vs_3954_, v___x_3955_, v___x_3956_);
lean_dec_ref(v_vs_3954_);
lean_dec_ref(v_ks_3953_);
return v___x_3957_;
}
else
{
return v_newNode_3950_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3965_, lean_object* v_keys_3966_, lean_object* v_vals_3967_, lean_object* v_i_3968_, lean_object* v_entries_3969_){
_start:
{
lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3970_ = lean_array_get_size(v_keys_3966_);
v___x_3971_ = lean_nat_dec_lt(v_i_3968_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_dec(v_i_3968_);
return v_entries_3969_;
}
else
{
lean_object* v_k_3972_; lean_object* v_v_3973_; uint64_t v___x_3974_; size_t v_h_3975_; size_t v___x_3976_; lean_object* v___x_3977_; size_t v___x_3978_; size_t v___x_3979_; size_t v___x_3980_; size_t v_h_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_k_3972_ = lean_array_fget_borrowed(v_keys_3966_, v_i_3968_);
v_v_3973_ = lean_array_fget_borrowed(v_vals_3967_, v_i_3968_);
v___x_3974_ = l_Lean_instHashableMVarId_hash(v_k_3972_);
v_h_3975_ = lean_uint64_to_usize(v___x_3974_);
v___x_3976_ = ((size_t)5ULL);
v___x_3977_ = lean_unsigned_to_nat(1u);
v___x_3978_ = ((size_t)1ULL);
v___x_3979_ = lean_usize_sub(v_depth_3965_, v___x_3978_);
v___x_3980_ = lean_usize_mul(v___x_3976_, v___x_3979_);
v_h_3981_ = lean_usize_shift_right(v_h_3975_, v___x_3980_);
v___x_3982_ = lean_nat_add(v_i_3968_, v___x_3977_);
lean_dec(v_i_3968_);
lean_inc(v_v_3973_);
lean_inc(v_k_3972_);
v___x_3983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3969_, v_h_3981_, v_depth_3965_, v_k_3972_, v_v_3973_);
v_i_3968_ = v___x_3982_;
v_entries_3969_ = v___x_3983_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3985_, lean_object* v_keys_3986_, lean_object* v_vals_3987_, lean_object* v_i_3988_, lean_object* v_entries_3989_){
_start:
{
size_t v_depth_boxed_3990_; lean_object* v_res_3991_; 
v_depth_boxed_3990_ = lean_unbox_usize(v_depth_3985_);
lean_dec(v_depth_3985_);
v_res_3991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3990_, v_keys_3986_, v_vals_3987_, v_i_3988_, v_entries_3989_);
lean_dec_ref(v_vals_3987_);
lean_dec_ref(v_keys_3986_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3992_, lean_object* v_x_3993_, lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
size_t v_x_2324__boxed_3997_; size_t v_x_2325__boxed_3998_; lean_object* v_res_3999_; 
v_x_2324__boxed_3997_ = lean_unbox_usize(v_x_3993_);
lean_dec(v_x_3993_);
v_x_2325__boxed_3998_ = lean_unbox_usize(v_x_3994_);
lean_dec(v_x_3994_);
v_res_3999_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3992_, v_x_2324__boxed_3997_, v_x_2325__boxed_3998_, v_x_3995_, v_x_3996_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_4000_, lean_object* v_x_4001_, lean_object* v_x_4002_){
_start:
{
uint64_t v___x_4003_; size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v___x_4003_ = l_Lean_instHashableMVarId_hash(v_x_4001_);
v___x_4004_ = lean_uint64_to_usize(v___x_4003_);
v___x_4005_ = ((size_t)1ULL);
v___x_4006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4000_, v___x_4004_, v___x_4005_, v_x_4001_, v_x_4002_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_4007_, lean_object* v_val_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; lean_object* v_mctx_4012_; lean_object* v_cache_4013_; lean_object* v_zetaDeltaFVarIds_4014_; lean_object* v_postponed_4015_; lean_object* v_diag_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4044_; 
v___x_4011_ = lean_st_ref_take(v___y_4009_);
v_mctx_4012_ = lean_ctor_get(v___x_4011_, 0);
v_cache_4013_ = lean_ctor_get(v___x_4011_, 1);
v_zetaDeltaFVarIds_4014_ = lean_ctor_get(v___x_4011_, 2);
v_postponed_4015_ = lean_ctor_get(v___x_4011_, 3);
v_diag_4016_ = lean_ctor_get(v___x_4011_, 4);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4018_ = v___x_4011_;
v_isShared_4019_ = v_isSharedCheck_4044_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_diag_4016_);
lean_inc(v_postponed_4015_);
lean_inc(v_zetaDeltaFVarIds_4014_);
lean_inc(v_cache_4013_);
lean_inc(v_mctx_4012_);
lean_dec(v___x_4011_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4044_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v_depth_4020_; lean_object* v_levelAssignDepth_4021_; lean_object* v_lmvarCounter_4022_; lean_object* v_mvarCounter_4023_; lean_object* v_lDecls_4024_; lean_object* v_decls_4025_; lean_object* v_userNames_4026_; lean_object* v_lAssignment_4027_; lean_object* v_eAssignment_4028_; lean_object* v_dAssignment_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4043_; 
v_depth_4020_ = lean_ctor_get(v_mctx_4012_, 0);
v_levelAssignDepth_4021_ = lean_ctor_get(v_mctx_4012_, 1);
v_lmvarCounter_4022_ = lean_ctor_get(v_mctx_4012_, 2);
v_mvarCounter_4023_ = lean_ctor_get(v_mctx_4012_, 3);
v_lDecls_4024_ = lean_ctor_get(v_mctx_4012_, 4);
v_decls_4025_ = lean_ctor_get(v_mctx_4012_, 5);
v_userNames_4026_ = lean_ctor_get(v_mctx_4012_, 6);
v_lAssignment_4027_ = lean_ctor_get(v_mctx_4012_, 7);
v_eAssignment_4028_ = lean_ctor_get(v_mctx_4012_, 8);
v_dAssignment_4029_ = lean_ctor_get(v_mctx_4012_, 9);
v_isSharedCheck_4043_ = !lean_is_exclusive(v_mctx_4012_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4031_ = v_mctx_4012_;
v_isShared_4032_ = v_isSharedCheck_4043_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_dAssignment_4029_);
lean_inc(v_eAssignment_4028_);
lean_inc(v_lAssignment_4027_);
lean_inc(v_userNames_4026_);
lean_inc(v_decls_4025_);
lean_inc(v_lDecls_4024_);
lean_inc(v_mvarCounter_4023_);
lean_inc(v_lmvarCounter_4022_);
lean_inc(v_levelAssignDepth_4021_);
lean_inc(v_depth_4020_);
lean_dec(v_mctx_4012_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4043_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4035_; 
v___x_4033_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_4028_, v_mvarId_4007_, v_val_4008_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 8, v___x_4033_);
v___x_4035_ = v___x_4031_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_depth_4020_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_levelAssignDepth_4021_);
lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_lmvarCounter_4022_);
lean_ctor_set(v_reuseFailAlloc_4042_, 3, v_mvarCounter_4023_);
lean_ctor_set(v_reuseFailAlloc_4042_, 4, v_lDecls_4024_);
lean_ctor_set(v_reuseFailAlloc_4042_, 5, v_decls_4025_);
lean_ctor_set(v_reuseFailAlloc_4042_, 6, v_userNames_4026_);
lean_ctor_set(v_reuseFailAlloc_4042_, 7, v_lAssignment_4027_);
lean_ctor_set(v_reuseFailAlloc_4042_, 8, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4042_, 9, v_dAssignment_4029_);
v___x_4035_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4035_);
v___x_4037_ = v___x_4018_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4035_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v_cache_4013_);
lean_ctor_set(v_reuseFailAlloc_4041_, 2, v_zetaDeltaFVarIds_4014_);
lean_ctor_set(v_reuseFailAlloc_4041_, 3, v_postponed_4015_);
lean_ctor_set(v_reuseFailAlloc_4041_, 4, v_diag_4016_);
v___x_4037_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4038_ = lean_st_ref_set(v___y_4009_, v___x_4037_);
v___x_4039_ = lean_box(0);
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
return v___x_4040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4045_, lean_object* v_val_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4045_, v_val_4046_, v___y_4047_);
lean_dec(v___y_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4050_, size_t v_i_4051_, lean_object* v_bs_4052_){
_start:
{
uint8_t v___x_4053_; 
v___x_4053_ = lean_usize_dec_lt(v_i_4051_, v_sz_4050_);
if (v___x_4053_ == 0)
{
return v_bs_4052_;
}
else
{
lean_object* v_v_4054_; lean_object* v___x_4055_; lean_object* v_bs_x27_4056_; lean_object* v___x_4057_; size_t v___x_4058_; size_t v___x_4059_; lean_object* v___x_4060_; 
v_v_4054_ = lean_array_uget(v_bs_4052_, v_i_4051_);
v___x_4055_ = lean_unsigned_to_nat(0u);
v_bs_x27_4056_ = lean_array_uset(v_bs_4052_, v_i_4051_, v___x_4055_);
v___x_4057_ = l_Lean_Expr_fvar___override(v_v_4054_);
v___x_4058_ = ((size_t)1ULL);
v___x_4059_ = lean_usize_add(v_i_4051_, v___x_4058_);
v___x_4060_ = lean_array_uset(v_bs_x27_4056_, v_i_4051_, v___x_4057_);
v_i_4051_ = v___x_4059_;
v_bs_4052_ = v___x_4060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4062_, lean_object* v_i_4063_, lean_object* v_bs_4064_){
_start:
{
size_t v_sz_boxed_4065_; size_t v_i_boxed_4066_; lean_object* v_res_4067_; 
v_sz_boxed_4065_ = lean_unbox_usize(v_sz_4062_);
lean_dec(v_sz_4062_);
v_i_boxed_4066_ = lean_unbox_usize(v_i_4063_);
lean_dec(v_i_4063_);
v_res_4067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4065_, v_i_boxed_4066_, v_bs_4064_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4068_, lean_object* v_mvarId_4069_, lean_object* v___x_4070_, lean_object* v_a_4071_, lean_object* v_fvarIds_4072_, lean_object* v_es_4073_, lean_object* v_givenNames_x27_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___y_4132_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v___x_4080_ = lean_unsigned_to_nat(0u);
v___x_4081_ = lean_array_get_borrowed(v___x_4068_, v_es_4073_, v___x_4080_);
v___x_4142_ = lean_array_get_size(v_fvarIds_4072_);
v___x_4143_ = lean_nat_dec_eq(v___x_4142_, v___x_4080_);
if (v___x_4143_ == 0)
{
v___y_4132_ = v___x_4143_;
goto v___jp_4131_;
}
else
{
uint8_t v___x_4144_; 
v___x_4144_ = lean_expr_eqv(v_a_4071_, v___x_4081_);
v___y_4132_ = v___x_4144_;
goto v___jp_4131_;
}
v___jp_4082_:
{
lean_object* v___x_4083_; 
lean_inc(v_mvarId_4069_);
v___x_4083_ = l_Lean_MVarId_getTag(v_mvarId_4069_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___x_4083_);
lean_inc(v___x_4081_);
v___x_4085_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4081_, v_a_4084_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v_a_4086_; size_t v_sz_4087_; size_t v___x_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; uint8_t v___x_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; 
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc_n(v_a_4086_, 2);
lean_dec_ref(v___x_4085_);
v_sz_4087_ = lean_array_size(v_fvarIds_4072_);
v___x_4088_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4072_);
v___x_4089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4087_, v___x_4088_, v_fvarIds_4072_);
v___x_4090_ = 0;
v___x_4091_ = 1;
v___x_4092_ = 1;
v___x_4093_ = l_Lean_Meta_mkLetFVars(v___x_4089_, v_a_4086_, v___x_4090_, v___x_4091_, v___x_4092_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec_ref(v___x_4089_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4105_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref(v___x_4093_);
v___x_4095_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4069_, v_a_4094_, v___y_4076_);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; 
v_unused_4106_ = lean_ctor_get(v___x_4095_, 0);
lean_dec(v_unused_4106_);
v___x_4097_ = v___x_4095_;
v_isShared_4098_ = v_isSharedCheck_4105_;
goto v_resetjp_4096_;
}
else
{
lean_dec(v___x_4095_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4105_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4103_; 
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v_fvarIds_4072_);
lean_ctor_set(v___x_4099_, 1, v_givenNames_x27_4074_);
v___x_4100_ = l_Lean_Expr_mvarId_x21(v_a_4086_);
lean_dec(v_a_4086_);
v___x_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4101_);
v___x_4103_ = v___x_4097_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v_a_4086_);
lean_dec(v_givenNames_x27_4074_);
lean_dec_ref(v_fvarIds_4072_);
lean_dec(v_mvarId_4069_);
v_a_4107_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4093_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4093_);
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
lean_dec(v_givenNames_x27_4074_);
lean_dec_ref(v_fvarIds_4072_);
lean_dec(v_mvarId_4069_);
v_a_4115_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4085_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4085_);
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
lean_dec(v_givenNames_x27_4074_);
lean_dec_ref(v_fvarIds_4072_);
lean_dec(v_mvarId_4069_);
v_a_4123_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4083_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4083_);
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
v___jp_4131_:
{
if (v___y_4132_ == 0)
{
lean_dec(v___x_4070_);
goto v___jp_4082_;
}
else
{
lean_object* v___x_4133_; 
lean_inc(v_mvarId_4069_);
v___x_4133_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4070_, v_mvarId_4069_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_dec_ref(v___x_4133_);
goto v___jp_4082_;
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec(v_givenNames_x27_4074_);
lean_dec_ref(v_fvarIds_4072_);
lean_dec(v_mvarId_4069_);
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4133_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4145_, lean_object* v_mvarId_4146_, lean_object* v___x_4147_, lean_object* v_a_4148_, lean_object* v_fvarIds_4149_, lean_object* v_es_4150_, lean_object* v_givenNames_x27_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_MVarId_extractLets___lam__0(v___x_4145_, v_mvarId_4146_, v___x_4147_, v_a_4148_, v_fvarIds_4149_, v_es_4150_, v_givenNames_x27_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_es_4150_);
lean_dec_ref(v_a_4148_);
lean_dec_ref(v___x_4145_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4158_, lean_object* v___x_4159_, lean_object* v___x_4160_, lean_object* v_givenNames_4161_, lean_object* v_config_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v___x_4168_; 
lean_inc(v___x_4159_);
lean_inc(v_mvarId_4158_);
v___x_4168_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4158_, v___x_4159_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v___x_4169_; 
lean_dec_ref(v___x_4168_);
lean_inc(v_mvarId_4158_);
v___x_4169_ = l_Lean_MVarId_getType(v_mvarId_4158_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___f_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc_n(v_a_4170_, 2);
lean_dec_ref(v___x_4169_);
v___f_4171_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4171_, 0, v___x_4160_);
lean_closure_set(v___f_4171_, 1, v_mvarId_4158_);
lean_closure_set(v___f_4171_, 2, v___x_4159_);
lean_closure_set(v___f_4171_, 3, v_a_4170_);
v___x_4172_ = lean_unsigned_to_nat(1u);
v___x_4173_ = lean_mk_empty_array_with_capacity(v___x_4172_);
v___x_4174_ = lean_array_push(v___x_4173_, v_a_4170_);
v___x_4175_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4174_, v_givenNames_4161_, v___f_4171_, v_config_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
return v___x_4175_;
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec(v_givenNames_4161_);
lean_dec_ref(v___x_4160_);
lean_dec(v___x_4159_);
lean_dec(v_mvarId_4158_);
v_a_4176_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4169_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4169_);
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
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec(v_givenNames_4161_);
lean_dec_ref(v___x_4160_);
lean_dec(v___x_4159_);
lean_dec(v_mvarId_4158_);
v_a_4184_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4168_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4168_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4192_, lean_object* v___x_4193_, lean_object* v___x_4194_, lean_object* v_givenNames_4195_, lean_object* v_config_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4192_, v___x_4193_, v___x_4194_, v_givenNames_4195_, v_config_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_config_4196_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4206_, lean_object* v_givenNames_4207_, lean_object* v_config_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___f_4216_; lean_object* v___x_4217_; 
v___x_4214_ = l_Lean_instInhabitedExpr;
v___x_4215_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4206_);
v___f_4216_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4216_, 0, v_mvarId_4206_);
lean_closure_set(v___f_4216_, 1, v___x_4215_);
lean_closure_set(v___f_4216_, 2, v___x_4214_);
lean_closure_set(v___f_4216_, 3, v_givenNames_4207_);
lean_closure_set(v___f_4216_, 4, v_config_4208_);
v___x_4217_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4206_, v___f_4216_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4218_, lean_object* v_givenNames_4219_, lean_object* v_config_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_MVarId_extractLets(v_mvarId_4218_, v_givenNames_4219_, v_config_4220_, v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_);
lean_dec(v_a_4224_);
lean_dec_ref(v_a_4223_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4227_, lean_object* v_val_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4227_, v_val_4228_, v___y_4230_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4235_, lean_object* v_val_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4235_, v_val_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4243_, lean_object* v_x_4244_, lean_object* v_x_4245_, lean_object* v_x_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4244_, v_x_4245_, v_x_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4248_, lean_object* v_x_4249_, size_t v_x_4250_, size_t v_x_4251_, lean_object* v_x_4252_, lean_object* v_x_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4249_, v_x_4250_, v_x_4251_, v_x_4252_, v_x_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4255_, lean_object* v_x_4256_, lean_object* v_x_4257_, lean_object* v_x_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_){
_start:
{
size_t v_x_2828__boxed_4261_; size_t v_x_2829__boxed_4262_; lean_object* v_res_4263_; 
v_x_2828__boxed_4261_ = lean_unbox_usize(v_x_4257_);
lean_dec(v_x_4257_);
v_x_2829__boxed_4262_ = lean_unbox_usize(v_x_4258_);
lean_dec(v_x_4258_);
v_res_4263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4255_, v_x_4256_, v_x_2828__boxed_4261_, v_x_2829__boxed_4262_, v_x_4259_, v_x_4260_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4264_, lean_object* v_n_4265_, lean_object* v_k_4266_, lean_object* v_v_4267_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4265_, v_k_4266_, v_v_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4269_, size_t v_depth_4270_, lean_object* v_keys_4271_, lean_object* v_vals_4272_, lean_object* v_heq_4273_, lean_object* v_i_4274_, lean_object* v_entries_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4270_, v_keys_4271_, v_vals_4272_, v_i_4274_, v_entries_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4277_, lean_object* v_depth_4278_, lean_object* v_keys_4279_, lean_object* v_vals_4280_, lean_object* v_heq_4281_, lean_object* v_i_4282_, lean_object* v_entries_4283_){
_start:
{
size_t v_depth_boxed_4284_; lean_object* v_res_4285_; 
v_depth_boxed_4284_ = lean_unbox_usize(v_depth_4278_);
lean_dec(v_depth_4278_);
v_res_4285_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4277_, v_depth_boxed_4284_, v_keys_4279_, v_vals_4280_, v_heq_4281_, v_i_4282_, v_entries_4283_);
lean_dec_ref(v_vals_4280_);
lean_dec_ref(v_keys_4279_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_, lean_object* v_x_4289_, lean_object* v_x_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4287_, v_x_4288_, v_x_4289_, v_x_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4292_, size_t v_i_4293_, lean_object* v_bs_4294_){
_start:
{
uint8_t v___x_4295_; 
v___x_4295_ = lean_usize_dec_lt(v_i_4293_, v_sz_4292_);
if (v___x_4295_ == 0)
{
return v_bs_4294_;
}
else
{
lean_object* v_v_4296_; lean_object* v___x_4297_; lean_object* v_bs_x27_4298_; lean_object* v___x_4299_; size_t v___x_4300_; size_t v___x_4301_; lean_object* v___x_4302_; 
v_v_4296_ = lean_array_uget(v_bs_4294_, v_i_4293_);
v___x_4297_ = lean_unsigned_to_nat(0u);
v_bs_x27_4298_ = lean_array_uset(v_bs_4294_, v_i_4293_, v___x_4297_);
v___x_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4299_, 0, v_v_4296_);
v___x_4300_ = ((size_t)1ULL);
v___x_4301_ = lean_usize_add(v_i_4293_, v___x_4300_);
v___x_4302_ = lean_array_uset(v_bs_x27_4298_, v_i_4293_, v___x_4299_);
v_i_4293_ = v___x_4301_;
v_bs_4294_ = v___x_4302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4304_, lean_object* v_i_4305_, lean_object* v_bs_4306_){
_start:
{
size_t v_sz_boxed_4307_; size_t v_i_boxed_4308_; lean_object* v_res_4309_; 
v_sz_boxed_4307_ = lean_unbox_usize(v_sz_4304_);
lean_dec(v_sz_4304_);
v_i_boxed_4308_ = lean_unbox_usize(v_i_4305_);
lean_dec(v_i_4305_);
v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4307_, v_i_boxed_4308_, v_bs_4306_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4310_, lean_object* v_fvars_4311_, lean_object* v_fvarIds_4312_, lean_object* v_givenNames_x27_4313_, lean_object* v_targetNew_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
lean_inc(v_mvarId_4310_);
v___x_4320_ = l_Lean_MVarId_getTag(v_mvarId_4310_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4322_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref(v___x_4320_);
v___x_4322_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4314_, v_a_4321_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; size_t v_sz_4324_; size_t v___x_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; uint8_t v___x_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc_n(v_a_4323_, 2);
lean_dec_ref(v___x_4322_);
v_sz_4324_ = lean_array_size(v_fvarIds_4312_);
v___x_4325_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4312_);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4324_, v___x_4325_, v_fvarIds_4312_);
v___x_4327_ = 0;
v___x_4328_ = 1;
v___x_4329_ = 1;
v___x_4330_ = l_Lean_Meta_mkLetFVars(v___x_4326_, v_a_4323_, v___x_4327_, v___x_4328_, v___x_4329_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec_ref(v___x_4326_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4345_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref(v___x_4330_);
v___x_4332_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4310_, v_a_4331_, v___y_4316_);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4345_ == 0)
{
lean_object* v_unused_4346_; 
v_unused_4346_ = lean_ctor_get(v___x_4332_, 0);
lean_dec(v_unused_4346_);
v___x_4334_ = v___x_4332_;
v_isShared_4335_ = v_isSharedCheck_4345_;
goto v_resetjp_4333_;
}
else
{
lean_dec(v___x_4332_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4345_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; size_t v_sz_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4336_, 0, v_fvarIds_4312_);
lean_ctor_set(v___x_4336_, 1, v_givenNames_x27_4313_);
v_sz_4337_ = lean_array_size(v_fvars_4311_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4337_, v___x_4325_, v_fvars_4311_);
v___x_4339_ = l_Lean_Expr_mvarId_x21(v_a_4323_);
lean_dec(v_a_4323_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4336_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v___x_4341_);
v___x_4343_ = v___x_4334_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec(v_a_4323_);
lean_dec(v_givenNames_x27_4313_);
lean_dec_ref(v_fvarIds_4312_);
lean_dec_ref(v_fvars_4311_);
lean_dec(v_mvarId_4310_);
v_a_4347_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4330_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4330_);
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
lean_dec(v_givenNames_x27_4313_);
lean_dec_ref(v_fvarIds_4312_);
lean_dec_ref(v_fvars_4311_);
lean_dec(v_mvarId_4310_);
v_a_4355_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4322_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4322_);
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
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec_ref(v_targetNew_4314_);
lean_dec(v_givenNames_x27_4313_);
lean_dec_ref(v_fvarIds_4312_);
lean_dec_ref(v_fvars_4311_);
lean_dec(v_mvarId_4310_);
v_a_4363_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4320_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4320_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4371_, lean_object* v_fvars_4372_, lean_object* v_fvarIds_4373_, lean_object* v_givenNames_x27_4374_, lean_object* v_targetNew_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4371_, v_fvars_4372_, v_fvarIds_4373_, v_givenNames_x27_4374_, v_targetNew_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4382_, lean_object* v_binderName_4383_, lean_object* v_body_4384_, uint8_t v_binderInfo_4385_, lean_object* v___f_4386_, lean_object* v___x_4387_, lean_object* v_mvarId_4388_, lean_object* v_binderType_4389_, lean_object* v_fvarIds_4390_, lean_object* v_es_4391_, lean_object* v_givenNames_x27_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___y_4404_; lean_object* v___x_4414_; uint8_t v___x_4415_; 
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = lean_array_get_borrowed(v___x_4382_, v_es_4391_, v___x_4398_);
v___x_4414_ = lean_array_get_size(v_fvarIds_4390_);
v___x_4415_ = lean_nat_dec_eq(v___x_4414_, v___x_4398_);
if (v___x_4415_ == 0)
{
v___y_4404_ = v___x_4415_;
goto v___jp_4403_;
}
else
{
uint8_t v___x_4416_; 
v___x_4416_ = lean_expr_eqv(v_binderType_4389_, v___x_4399_);
v___y_4404_ = v___x_4416_;
goto v___jp_4403_;
}
v___jp_4400_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
lean_inc(v___x_4399_);
v___x_4401_ = l_Lean_Expr_forallE___override(v_binderName_4383_, v___x_4399_, v_body_4384_, v_binderInfo_4385_);
lean_inc(v___y_4396_);
lean_inc_ref(v___y_4395_);
lean_inc(v___y_4394_);
lean_inc_ref(v___y_4393_);
v___x_4402_ = lean_apply_8(v___f_4386_, v_fvarIds_4390_, v_givenNames_x27_4392_, v___x_4401_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, lean_box(0));
return v___x_4402_;
}
v___jp_4403_:
{
if (v___y_4404_ == 0)
{
lean_dec(v_mvarId_4388_);
lean_dec(v___x_4387_);
goto v___jp_4400_;
}
else
{
lean_object* v___x_4405_; 
v___x_4405_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4387_, v_mvarId_4388_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_dec_ref(v___x_4405_);
goto v___jp_4400_;
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
lean_dec(v_givenNames_x27_4392_);
lean_dec_ref(v_fvarIds_4390_);
lean_dec_ref(v___f_4386_);
lean_dec_ref(v_body_4384_);
lean_dec(v_binderName_4383_);
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4405_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4405_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4417_, lean_object* v_binderName_4418_, lean_object* v_body_4419_, lean_object* v_binderInfo_4420_, lean_object* v___f_4421_, lean_object* v___x_4422_, lean_object* v_mvarId_4423_, lean_object* v_binderType_4424_, lean_object* v_fvarIds_4425_, lean_object* v_es_4426_, lean_object* v_givenNames_x27_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
uint8_t v_binderInfo_1854__boxed_4433_; lean_object* v_res_4434_; 
v_binderInfo_1854__boxed_4433_ = lean_unbox(v_binderInfo_4420_);
v_res_4434_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4417_, v_binderName_4418_, v_body_4419_, v_binderInfo_1854__boxed_4433_, v___f_4421_, v___x_4422_, v_mvarId_4423_, v_binderType_4424_, v_fvarIds_4425_, v_es_4426_, v_givenNames_x27_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec_ref(v_es_4426_);
lean_dec_ref(v_binderType_4424_);
lean_dec_ref(v___x_4417_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4435_, lean_object* v_declName_4436_, lean_object* v_body_4437_, uint8_t v_nondep_4438_, lean_object* v___f_4439_, lean_object* v_value_4440_, lean_object* v___x_4441_, lean_object* v_mvarId_4442_, lean_object* v_type_4443_, lean_object* v_fvarIds_4444_, lean_object* v_es_4445_, lean_object* v_givenNames_x27_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; uint8_t v___y_4460_; lean_object* v___x_4471_; uint8_t v___x_4472_; 
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = lean_array_get_borrowed(v___x_4435_, v_es_4445_, v___x_4452_);
v___x_4454_ = lean_unsigned_to_nat(1u);
v___x_4455_ = lean_array_get_borrowed(v___x_4435_, v_es_4445_, v___x_4454_);
v___x_4471_ = lean_array_get_size(v_fvarIds_4444_);
v___x_4472_ = lean_nat_dec_eq(v___x_4471_, v___x_4452_);
if (v___x_4472_ == 0)
{
v___y_4460_ = v___x_4472_;
goto v___jp_4459_;
}
else
{
uint8_t v___x_4473_; 
v___x_4473_ = lean_expr_eqv(v_type_4443_, v___x_4453_);
v___y_4460_ = v___x_4473_;
goto v___jp_4459_;
}
v___jp_4456_:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; 
lean_inc(v___x_4455_);
lean_inc(v___x_4453_);
v___x_4457_ = l_Lean_Expr_letE___override(v_declName_4436_, v___x_4453_, v___x_4455_, v_body_4437_, v_nondep_4438_);
lean_inc(v___y_4450_);
lean_inc_ref(v___y_4449_);
lean_inc(v___y_4448_);
lean_inc_ref(v___y_4447_);
v___x_4458_ = lean_apply_8(v___f_4439_, v_fvarIds_4444_, v_givenNames_x27_4446_, v___x_4457_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, lean_box(0));
return v___x_4458_;
}
v___jp_4459_:
{
if (v___y_4460_ == 0)
{
lean_dec(v_mvarId_4442_);
lean_dec(v___x_4441_);
goto v___jp_4456_;
}
else
{
uint8_t v___x_4461_; 
v___x_4461_ = lean_expr_eqv(v_value_4440_, v___x_4455_);
if (v___x_4461_ == 0)
{
lean_dec(v_mvarId_4442_);
lean_dec(v___x_4441_);
goto v___jp_4456_;
}
else
{
lean_object* v___x_4462_; 
v___x_4462_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4441_, v_mvarId_4442_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_dec_ref(v___x_4462_);
goto v___jp_4456_;
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec(v_givenNames_x27_4446_);
lean_dec_ref(v_fvarIds_4444_);
lean_dec_ref(v___f_4439_);
lean_dec_ref(v_body_4437_);
lean_dec(v_declName_4436_);
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4462_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4462_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4474_ = _args[0];
lean_object* v_declName_4475_ = _args[1];
lean_object* v_body_4476_ = _args[2];
lean_object* v_nondep_4477_ = _args[3];
lean_object* v___f_4478_ = _args[4];
lean_object* v_value_4479_ = _args[5];
lean_object* v___x_4480_ = _args[6];
lean_object* v_mvarId_4481_ = _args[7];
lean_object* v_type_4482_ = _args[8];
lean_object* v_fvarIds_4483_ = _args[9];
lean_object* v_es_4484_ = _args[10];
lean_object* v_givenNames_x27_4485_ = _args[11];
lean_object* v___y_4486_ = _args[12];
lean_object* v___y_4487_ = _args[13];
lean_object* v___y_4488_ = _args[14];
lean_object* v___y_4489_ = _args[15];
lean_object* v___y_4490_ = _args[16];
_start:
{
uint8_t v_nondep_1929__boxed_4491_; lean_object* v_res_4492_; 
v_nondep_1929__boxed_4491_ = lean_unbox(v_nondep_4477_);
v_res_4492_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4474_, v_declName_4475_, v_body_4476_, v_nondep_1929__boxed_4491_, v___f_4478_, v_value_4479_, v___x_4480_, v_mvarId_4481_, v_type_4482_, v_fvarIds_4483_, v_es_4484_, v_givenNames_x27_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v_es_4484_);
lean_dec_ref(v_type_4482_);
lean_dec_ref(v_value_4479_);
lean_dec_ref(v___x_4474_);
return v_res_4492_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4496_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4497_ = l_Lean_MessageData_ofFormat(v___x_4496_);
return v___x_4497_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4498_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4500_, lean_object* v___x_4501_, lean_object* v___f_4502_, lean_object* v___x_4503_, lean_object* v_givenNames_4504_, lean_object* v_config_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v___x_4511_; 
lean_inc(v_mvarId_4500_);
v___x_4511_ = l_Lean_MVarId_getType(v_mvarId_4500_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref(v___x_4511_);
switch(lean_obj_tag(v_a_4512_))
{
case 7:
{
lean_object* v_binderName_4513_; lean_object* v_binderType_4514_; lean_object* v_body_4515_; uint8_t v_binderInfo_4516_; lean_object* v___x_4517_; lean_object* v___f_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_binderName_4513_ = lean_ctor_get(v_a_4512_, 0);
lean_inc(v_binderName_4513_);
v_binderType_4514_ = lean_ctor_get(v_a_4512_, 1);
lean_inc_ref_n(v_binderType_4514_, 2);
v_body_4515_ = lean_ctor_get(v_a_4512_, 2);
lean_inc_ref(v_body_4515_);
v_binderInfo_4516_ = lean_ctor_get_uint8(v_a_4512_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4512_);
v___x_4517_ = lean_box(v_binderInfo_4516_);
v___f_4518_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4518_, 0, v___x_4501_);
lean_closure_set(v___f_4518_, 1, v_binderName_4513_);
lean_closure_set(v___f_4518_, 2, v_body_4515_);
lean_closure_set(v___f_4518_, 3, v___x_4517_);
lean_closure_set(v___f_4518_, 4, v___f_4502_);
lean_closure_set(v___f_4518_, 5, v___x_4503_);
lean_closure_set(v___f_4518_, 6, v_mvarId_4500_);
lean_closure_set(v___f_4518_, 7, v_binderType_4514_);
v___x_4519_ = lean_unsigned_to_nat(1u);
v___x_4520_ = lean_mk_empty_array_with_capacity(v___x_4519_);
v___x_4521_ = lean_array_push(v___x_4520_, v_binderType_4514_);
v___x_4522_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4521_, v_givenNames_4504_, v___f_4518_, v_config_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
return v___x_4522_;
}
case 8:
{
lean_object* v_declName_4523_; lean_object* v_type_4524_; lean_object* v_value_4525_; lean_object* v_body_4526_; uint8_t v_nondep_4527_; lean_object* v___x_4528_; lean_object* v___f_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v_declName_4523_ = lean_ctor_get(v_a_4512_, 0);
lean_inc(v_declName_4523_);
v_type_4524_ = lean_ctor_get(v_a_4512_, 1);
lean_inc_ref_n(v_type_4524_, 2);
v_value_4525_ = lean_ctor_get(v_a_4512_, 2);
lean_inc_ref_n(v_value_4525_, 2);
v_body_4526_ = lean_ctor_get(v_a_4512_, 3);
lean_inc_ref(v_body_4526_);
v_nondep_4527_ = lean_ctor_get_uint8(v_a_4512_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4512_);
v___x_4528_ = lean_box(v_nondep_4527_);
v___f_4529_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4529_, 0, v___x_4501_);
lean_closure_set(v___f_4529_, 1, v_declName_4523_);
lean_closure_set(v___f_4529_, 2, v_body_4526_);
lean_closure_set(v___f_4529_, 3, v___x_4528_);
lean_closure_set(v___f_4529_, 4, v___f_4502_);
lean_closure_set(v___f_4529_, 5, v_value_4525_);
lean_closure_set(v___f_4529_, 6, v___x_4503_);
lean_closure_set(v___f_4529_, 7, v_mvarId_4500_);
lean_closure_set(v___f_4529_, 8, v_type_4524_);
v___x_4530_ = lean_unsigned_to_nat(2u);
v___x_4531_ = lean_mk_empty_array_with_capacity(v___x_4530_);
v___x_4532_ = lean_array_push(v___x_4531_, v_type_4524_);
v___x_4533_ = lean_array_push(v___x_4532_, v_value_4525_);
v___x_4534_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4533_, v_givenNames_4504_, v___f_4529_, v_config_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
return v___x_4534_;
}
default: 
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_dec(v_a_4512_);
lean_dec(v_givenNames_4504_);
lean_dec_ref(v___f_4502_);
lean_dec_ref(v___x_4501_);
v___x_4535_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4536_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4503_, v_mvarId_4500_, v___x_4535_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
return v___x_4536_;
}
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_dec(v_givenNames_4504_);
lean_dec(v___x_4503_);
lean_dec_ref(v___f_4502_);
lean_dec_ref(v___x_4501_);
lean_dec(v_mvarId_4500_);
v_a_4537_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4511_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4511_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4545_, lean_object* v___x_4546_, lean_object* v___f_4547_, lean_object* v___x_4548_, lean_object* v_givenNames_4549_, lean_object* v_config_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4545_, v___x_4546_, v___f_4547_, v___x_4548_, v_givenNames_4549_, v_config_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec_ref(v_config_4550_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4557_, lean_object* v___x_4558_, lean_object* v_givenNames_4559_, lean_object* v_config_4560_, lean_object* v_mvarId_4561_, lean_object* v_fvars_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v___f_4568_; lean_object* v___f_4569_; lean_object* v___x_4570_; 
lean_inc_n(v_mvarId_4561_, 2);
v___f_4568_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4568_, 0, v_mvarId_4561_);
lean_closure_set(v___f_4568_, 1, v_fvars_4562_);
v___f_4569_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4569_, 0, v_mvarId_4561_);
lean_closure_set(v___f_4569_, 1, v___x_4557_);
lean_closure_set(v___f_4569_, 2, v___f_4568_);
lean_closure_set(v___f_4569_, 3, v___x_4558_);
lean_closure_set(v___f_4569_, 4, v_givenNames_4559_);
lean_closure_set(v___f_4569_, 5, v_config_4560_);
v___x_4570_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4561_, v___f_4569_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4571_, lean_object* v___x_4572_, lean_object* v_givenNames_4573_, lean_object* v_config_4574_, lean_object* v_mvarId_4575_, lean_object* v_fvars_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4571_, v___x_4572_, v_givenNames_4573_, v_config_4574_, v_mvarId_4575_, v_fvars_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4583_, lean_object* v_fvarId_4584_, lean_object* v_givenNames_4585_, lean_object* v_config_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4583_);
v___x_4593_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4583_, v___x_4592_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v___x_4594_; lean_object* v___f_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; lean_object* v___x_4600_; 
lean_dec_ref(v___x_4593_);
v___x_4594_ = l_Lean_instInhabitedExpr;
v___f_4595_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4595_, 0, v___x_4594_);
lean_closure_set(v___f_4595_, 1, v___x_4592_);
lean_closure_set(v___f_4595_, 2, v_givenNames_4585_);
lean_closure_set(v___f_4595_, 3, v_config_4586_);
v___x_4596_ = lean_unsigned_to_nat(1u);
v___x_4597_ = lean_mk_empty_array_with_capacity(v___x_4596_);
v___x_4598_ = lean_array_push(v___x_4597_, v_fvarId_4584_);
v___x_4599_ = 0;
v___x_4600_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4583_, v___x_4598_, v___f_4595_, v___x_4599_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4600_;
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec_ref(v_config_4586_);
lean_dec(v_givenNames_4585_);
lean_dec(v_fvarId_4584_);
lean_dec(v_mvarId_4583_);
v_a_4601_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4593_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4593_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4609_, lean_object* v_fvarId_4610_, lean_object* v_givenNames_4611_, lean_object* v_config_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4609_, v_fvarId_4610_, v_givenNames_4611_, v_config_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4619_, lean_object* v___x_4620_, lean_object* v_config_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v___x_4627_; 
lean_inc(v___x_4620_);
lean_inc(v_mvarId_4619_);
v___x_4627_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4619_, v___x_4620_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v___x_4628_; 
lean_dec_ref(v___x_4627_);
lean_inc(v_mvarId_4619_);
v___x_4628_ = l_Lean_MVarId_getType(v_mvarId_4619_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4630_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc_n(v_a_4629_, 2);
lean_dec_ref(v___x_4628_);
v___x_4630_ = l_Lean_Meta_liftLets(v_a_4629_, v_config_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4630_) == 0)
{
lean_object* v_a_4631_; uint8_t v___x_4632_; 
v_a_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_a_4631_);
lean_dec_ref(v___x_4630_);
v___x_4632_ = lean_expr_eqv(v_a_4629_, v_a_4631_);
lean_dec(v_a_4629_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
lean_dec(v___x_4620_);
v___x_4633_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4619_, v_a_4631_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
return v___x_4633_;
}
else
{
lean_object* v___x_4634_; 
lean_inc(v_mvarId_4619_);
v___x_4634_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4620_, v_mvarId_4619_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v___x_4635_; 
lean_dec_ref(v___x_4634_);
v___x_4635_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4619_, v_a_4631_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
return v___x_4635_;
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_a_4631_);
lean_dec(v_mvarId_4619_);
v_a_4636_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4634_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4634_);
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
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec(v_a_4629_);
lean_dec(v___x_4620_);
lean_dec(v_mvarId_4619_);
v_a_4644_ = lean_ctor_get(v___x_4630_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4630_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4630_);
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
lean_dec_ref(v_config_4621_);
lean_dec(v___x_4620_);
lean_dec(v_mvarId_4619_);
v_a_4652_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4628_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4628_);
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
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec_ref(v_config_4621_);
lean_dec(v___x_4620_);
lean_dec(v_mvarId_4619_);
v_a_4660_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4627_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4627_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4668_, lean_object* v___x_4669_, lean_object* v_config_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4668_, v___x_4669_, v_config_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4680_, lean_object* v_config_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v___x_4687_; lean_object* v___f_4688_; lean_object* v___x_4689_; 
v___x_4687_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4680_);
v___f_4688_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4688_, 0, v_mvarId_4680_);
lean_closure_set(v___f_4688_, 1, v___x_4687_);
lean_closure_set(v___f_4688_, 2, v_config_4681_);
v___x_4689_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4680_, v___f_4688_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4690_, lean_object* v_config_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_MVarId_liftLets(v_mvarId_4690_, v_config_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4698_, lean_object* v_fvars_4699_, lean_object* v_targetNew_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4698_, v_targetNew_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4720_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4709_ = v___x_4706_;
v_isShared_4710_ = v_isSharedCheck_4720_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4706_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4720_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4711_; size_t v_sz_4712_; size_t v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4718_; 
v___x_4711_ = lean_box(0);
v_sz_4712_ = lean_array_size(v_fvars_4699_);
v___x_4713_ = ((size_t)0ULL);
v___x_4714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4712_, v___x_4713_, v_fvars_4699_);
v___x_4715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
lean_ctor_set(v___x_4715_, 1, v_a_4707_);
v___x_4716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4711_);
lean_ctor_set(v___x_4716_, 1, v___x_4715_);
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4716_);
v___x_4718_ = v___x_4709_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec_ref(v_fvars_4699_);
v_a_4721_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4706_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4706_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4729_, lean_object* v_fvars_4730_, lean_object* v_targetNew_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4729_, v_fvars_4730_, v_targetNew_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4738_, lean_object* v_config_4739_, lean_object* v___f_4740_, lean_object* v___x_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v___x_4747_; 
lean_inc(v_mvarId_4738_);
v___x_4747_ = l_Lean_MVarId_getType(v_mvarId_4738_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v___x_4747_);
switch(lean_obj_tag(v_a_4748_))
{
case 7:
{
lean_object* v_binderName_4749_; lean_object* v_binderType_4750_; lean_object* v_body_4751_; uint8_t v_binderInfo_4752_; lean_object* v___x_4753_; 
v_binderName_4749_ = lean_ctor_get(v_a_4748_, 0);
lean_inc(v_binderName_4749_);
v_binderType_4750_ = lean_ctor_get(v_a_4748_, 1);
lean_inc_ref_n(v_binderType_4750_, 2);
v_body_4751_ = lean_ctor_get(v_a_4748_, 2);
lean_inc_ref(v_body_4751_);
v_binderInfo_4752_ = lean_ctor_get_uint8(v_a_4748_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4748_);
v___x_4753_ = l_Lean_Meta_liftLets(v_binderType_4750_, v_config_4739_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; uint8_t v___x_4762_; 
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
lean_inc(v_a_4754_);
lean_dec_ref(v___x_4753_);
v___x_4762_ = lean_expr_eqv(v_binderType_4750_, v_a_4754_);
lean_dec_ref(v_binderType_4750_);
if (v___x_4762_ == 0)
{
lean_dec(v___x_4741_);
lean_dec(v_mvarId_4738_);
v___y_4756_ = v___y_4742_;
v___y_4757_ = v___y_4743_;
v___y_4758_ = v___y_4744_;
v___y_4759_ = v___y_4745_;
goto v___jp_4755_;
}
else
{
lean_object* v___x_4763_; 
v___x_4763_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4741_, v_mvarId_4738_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_dec_ref(v___x_4763_);
v___y_4756_ = v___y_4742_;
v___y_4757_ = v___y_4743_;
v___y_4758_ = v___y_4744_;
v___y_4759_ = v___y_4745_;
goto v___jp_4755_;
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_dec(v_a_4754_);
lean_dec_ref(v_body_4751_);
lean_dec(v_binderName_4749_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec_ref(v___f_4740_);
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4763_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4763_);
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
v___jp_4755_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4760_ = l_Lean_Expr_forallE___override(v_binderName_4749_, v_a_4754_, v_body_4751_, v_binderInfo_4752_);
v___x_4761_ = lean_apply_6(v___f_4740_, v___x_4760_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, lean_box(0));
return v___x_4761_;
}
}
else
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4779_; 
lean_dec_ref(v_body_4751_);
lean_dec_ref(v_binderType_4750_);
lean_dec(v_binderName_4749_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___x_4741_);
lean_dec_ref(v___f_4740_);
lean_dec(v_mvarId_4738_);
v_a_4772_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4774_ = v___x_4753_;
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4753_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4777_; 
if (v_isShared_4775_ == 0)
{
v___x_4777_ = v___x_4774_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4772_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
}
case 8:
{
lean_object* v_declName_4780_; lean_object* v_type_4781_; lean_object* v_value_4782_; lean_object* v_body_4783_; uint8_t v_nondep_4784_; lean_object* v___x_4785_; 
v_declName_4780_ = lean_ctor_get(v_a_4748_, 0);
lean_inc(v_declName_4780_);
v_type_4781_ = lean_ctor_get(v_a_4748_, 1);
lean_inc_ref_n(v_type_4781_, 2);
v_value_4782_ = lean_ctor_get(v_a_4748_, 2);
lean_inc_ref(v_value_4782_);
v_body_4783_ = lean_ctor_get(v_a_4748_, 3);
lean_inc_ref(v_body_4783_);
v_nondep_4784_ = lean_ctor_get_uint8(v_a_4748_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4748_);
lean_inc_ref(v_config_4739_);
v___x_4785_ = l_Lean_Meta_liftLets(v_type_4781_, v_config_4739_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4787_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref(v___x_4785_);
lean_inc_ref(v_value_4782_);
v___x_4787_ = l_Lean_Meta_liftLets(v_value_4782_, v_config_4739_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; uint8_t v___y_4797_; uint8_t v___x_4807_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref(v___x_4787_);
v___x_4807_ = lean_expr_eqv(v_type_4781_, v_a_4786_);
lean_dec_ref(v_type_4781_);
if (v___x_4807_ == 0)
{
lean_dec_ref(v_value_4782_);
v___y_4797_ = v___x_4807_;
goto v___jp_4796_;
}
else
{
uint8_t v___x_4808_; 
v___x_4808_ = lean_expr_eqv(v_value_4782_, v_a_4788_);
lean_dec_ref(v_value_4782_);
v___y_4797_ = v___x_4808_;
goto v___jp_4796_;
}
v___jp_4789_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = l_Lean_Expr_letE___override(v_declName_4780_, v_a_4786_, v_a_4788_, v_body_4783_, v_nondep_4784_);
v___x_4795_ = lean_apply_6(v___f_4740_, v___x_4794_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, lean_box(0));
return v___x_4795_;
}
v___jp_4796_:
{
if (v___y_4797_ == 0)
{
lean_dec(v___x_4741_);
lean_dec(v_mvarId_4738_);
v___y_4790_ = v___y_4742_;
v___y_4791_ = v___y_4743_;
v___y_4792_ = v___y_4744_;
v___y_4793_ = v___y_4745_;
goto v___jp_4789_;
}
else
{
lean_object* v___x_4798_; 
v___x_4798_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4741_, v_mvarId_4738_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_dec_ref(v___x_4798_);
v___y_4790_ = v___y_4742_;
v___y_4791_ = v___y_4743_;
v___y_4792_ = v___y_4744_;
v___y_4793_ = v___y_4745_;
goto v___jp_4789_;
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec(v_a_4788_);
lean_dec(v_a_4786_);
lean_dec_ref(v_body_4783_);
lean_dec(v_declName_4780_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec_ref(v___f_4740_);
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4798_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4798_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
}
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_dec(v_a_4786_);
lean_dec_ref(v_body_4783_);
lean_dec_ref(v_value_4782_);
lean_dec_ref(v_type_4781_);
lean_dec(v_declName_4780_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___x_4741_);
lean_dec_ref(v___f_4740_);
lean_dec(v_mvarId_4738_);
v_a_4809_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4787_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4787_);
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
lean_dec_ref(v_body_4783_);
lean_dec_ref(v_value_4782_);
lean_dec_ref(v_type_4781_);
lean_dec(v_declName_4780_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___x_4741_);
lean_dec_ref(v___f_4740_);
lean_dec_ref(v_config_4739_);
lean_dec(v_mvarId_4738_);
v_a_4817_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4785_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4785_);
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
default: 
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
lean_dec(v_a_4748_);
lean_dec_ref(v___f_4740_);
lean_dec_ref(v_config_4739_);
v___x_4825_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4826_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4741_, v_mvarId_4738_, v___x_4825_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
return v___x_4826_;
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___x_4741_);
lean_dec_ref(v___f_4740_);
lean_dec_ref(v_config_4739_);
lean_dec(v_mvarId_4738_);
v_a_4827_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4747_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4747_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4835_, lean_object* v_config_4836_, lean_object* v___f_4837_, lean_object* v___x_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4835_, v_config_4836_, v___f_4837_, v___x_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4845_, lean_object* v___x_4846_, lean_object* v_mvarId_4847_, lean_object* v_fvars_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v___f_4854_; lean_object* v___f_4855_; lean_object* v___x_4856_; 
lean_inc_n(v_mvarId_4847_, 2);
v___f_4854_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4854_, 0, v_mvarId_4847_);
lean_closure_set(v___f_4854_, 1, v_fvars_4848_);
v___f_4855_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4855_, 0, v_mvarId_4847_);
lean_closure_set(v___f_4855_, 1, v_config_4845_);
lean_closure_set(v___f_4855_, 2, v___f_4854_);
lean_closure_set(v___f_4855_, 3, v___x_4846_);
v___x_4856_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4847_, v___f_4855_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4857_, lean_object* v___x_4858_, lean_object* v_mvarId_4859_, lean_object* v_fvars_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4857_, v___x_4858_, v_mvarId_4859_, v_fvars_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4867_, lean_object* v_fvarId_4868_, lean_object* v_config_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4867_);
v___x_4876_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4867_, v___x_4875_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v___f_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; uint8_t v___x_4881_; lean_object* v___x_4882_; 
lean_dec_ref(v___x_4876_);
v___f_4877_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4877_, 0, v_config_4869_);
lean_closure_set(v___f_4877_, 1, v___x_4875_);
v___x_4878_ = lean_unsigned_to_nat(1u);
v___x_4879_ = lean_mk_empty_array_with_capacity(v___x_4878_);
v___x_4880_ = lean_array_push(v___x_4879_, v_fvarId_4868_);
v___x_4881_ = 0;
v___x_4882_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4867_, v___x_4880_, v___f_4877_, v___x_4881_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4891_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4885_ = v___x_4882_;
v_isShared_4886_ = v_isSharedCheck_4891_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4882_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4891_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v_snd_4887_; lean_object* v___x_4889_; 
v_snd_4887_ = lean_ctor_get(v_a_4883_, 1);
lean_inc(v_snd_4887_);
lean_dec(v_a_4883_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 0, v_snd_4887_);
v___x_4889_ = v___x_4885_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_snd_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
v_a_4892_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4882_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4882_);
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
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
lean_dec_ref(v_config_4869_);
lean_dec(v_fvarId_4868_);
lean_dec(v_mvarId_4867_);
v_a_4900_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4876_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4876_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4908_, lean_object* v_fvarId_4909_, lean_object* v_config_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4908_, v_fvarId_4909_, v_config_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4917_, lean_object* v___x_4918_, uint8_t v_failIfUnchanged_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v___x_4925_; 
lean_inc(v___x_4918_);
lean_inc(v_mvarId_4917_);
v___x_4925_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4917_, v___x_4918_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v___x_4926_; 
lean_dec_ref(v___x_4925_);
lean_inc(v_mvarId_4917_);
v___x_4926_ = l_Lean_MVarId_getType(v_mvarId_4917_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4928_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
lean_inc_n(v_a_4927_, 2);
lean_dec_ref(v___x_4926_);
v___x_4928_ = l_Lean_Meta_letToHave(v_a_4927_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4928_) == 0)
{
if (v_failIfUnchanged_4919_ == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
lean_dec(v_a_4927_);
lean_dec(v___x_4918_);
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref(v___x_4928_);
v___x_4930_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4917_, v_a_4929_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
return v___x_4930_;
}
else
{
lean_object* v_a_4931_; uint8_t v___x_4932_; 
v_a_4931_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4931_);
lean_dec_ref(v___x_4928_);
v___x_4932_ = lean_expr_eqv(v_a_4927_, v_a_4931_);
lean_dec(v_a_4927_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; 
lean_dec(v___x_4918_);
v___x_4933_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4917_, v_a_4931_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
return v___x_4933_;
}
else
{
lean_object* v___x_4934_; 
lean_inc(v_mvarId_4917_);
v___x_4934_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4918_, v_mvarId_4917_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v___x_4935_; 
lean_dec_ref(v___x_4934_);
v___x_4935_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4917_, v_a_4931_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
return v___x_4935_;
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
lean_dec(v_a_4931_);
lean_dec(v_mvarId_4917_);
v_a_4936_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4934_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4934_);
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
}
}
else
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4951_; 
lean_dec(v_a_4927_);
lean_dec(v___x_4918_);
lean_dec(v_mvarId_4917_);
v_a_4944_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4946_ = v___x_4928_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4928_);
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
lean_dec(v___x_4918_);
lean_dec(v_mvarId_4917_);
v_a_4952_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4926_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4926_);
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
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
lean_dec(v___x_4918_);
lean_dec(v_mvarId_4917_);
v_a_4960_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4925_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4925_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4968_, lean_object* v___x_4969_, lean_object* v_failIfUnchanged_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4976_; lean_object* v_res_4977_; 
v_failIfUnchanged_boxed_4976_ = lean_unbox(v_failIfUnchanged_4970_);
v_res_4977_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4968_, v___x_4969_, v_failIfUnchanged_boxed_4976_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4981_, uint8_t v_failIfUnchanged_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___f_4990_; lean_object* v___x_4991_; 
v___x_4988_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4989_ = lean_box(v_failIfUnchanged_4982_);
lean_inc(v_mvarId_4981_);
v___f_4990_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4990_, 0, v_mvarId_4981_);
lean_closure_set(v___f_4990_, 1, v___x_4988_);
lean_closure_set(v___f_4990_, 2, v___x_4989_);
v___x_4991_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4981_, v___f_4990_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4992_, lean_object* v_failIfUnchanged_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4999_; lean_object* v_res_5000_; 
v_failIfUnchanged_boxed_4999_ = lean_unbox(v_failIfUnchanged_4993_);
v_res_5000_ = l_Lean_MVarId_letToHave(v_mvarId_4992_, v_failIfUnchanged_boxed_4999_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_5001_, lean_object* v___x_5002_, lean_object* v_fvarId_5003_, uint8_t v_failIfUnchanged_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v___x_5010_; 
lean_inc(v___x_5002_);
lean_inc(v_mvarId_5001_);
v___x_5010_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_5001_, v___x_5002_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v___x_5011_; 
lean_dec_ref(v___x_5010_);
lean_inc(v_fvarId_5003_);
v___x_5011_ = l_Lean_FVarId_getType___redArg(v_fvarId_5003_, v___y_5005_, v___y_5007_, v___y_5008_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc_n(v_a_5012_, 2);
lean_dec_ref(v___x_5011_);
v___x_5013_ = l_Lean_Meta_letToHave(v_a_5012_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
if (lean_obj_tag(v___x_5013_) == 0)
{
if (v_failIfUnchanged_5004_ == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5015_; 
lean_dec(v_a_5012_);
lean_dec(v___x_5002_);
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc(v_a_5014_);
lean_dec_ref(v___x_5013_);
v___x_5015_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5001_, v_fvarId_5003_, v_a_5014_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
return v___x_5015_;
}
else
{
lean_object* v_a_5016_; uint8_t v___x_5017_; 
v_a_5016_ = lean_ctor_get(v___x_5013_, 0);
lean_inc(v_a_5016_);
lean_dec_ref(v___x_5013_);
v___x_5017_ = lean_expr_eqv(v_a_5012_, v_a_5016_);
lean_dec(v_a_5012_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; 
lean_dec(v___x_5002_);
v___x_5018_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5001_, v_fvarId_5003_, v_a_5016_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
return v___x_5018_;
}
else
{
lean_object* v___x_5019_; 
lean_inc(v_mvarId_5001_);
v___x_5019_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_5002_, v_mvarId_5001_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v___x_5020_; 
lean_dec_ref(v___x_5019_);
v___x_5020_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5001_, v_fvarId_5003_, v_a_5016_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
return v___x_5020_;
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_a_5016_);
lean_dec(v_fvarId_5003_);
lean_dec(v_mvarId_5001_);
v_a_5021_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_5019_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5019_);
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
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec(v_a_5012_);
lean_dec(v_fvarId_5003_);
lean_dec(v___x_5002_);
lean_dec(v_mvarId_5001_);
v_a_5029_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5013_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5013_);
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
lean_dec(v_fvarId_5003_);
lean_dec(v___x_5002_);
lean_dec(v_mvarId_5001_);
v_a_5037_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5039_ = v___x_5011_;
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5011_);
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
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_dec(v_fvarId_5003_);
lean_dec(v___x_5002_);
lean_dec(v_mvarId_5001_);
v_a_5045_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5010_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5010_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5053_, lean_object* v___x_5054_, lean_object* v_fvarId_5055_, lean_object* v_failIfUnchanged_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5062_; lean_object* v_res_5063_; 
v_failIfUnchanged_boxed_5062_ = lean_unbox(v_failIfUnchanged_5056_);
v_res_5063_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5053_, v___x_5054_, v_fvarId_5055_, v_failIfUnchanged_boxed_5062_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
lean_dec(v___y_5060_);
lean_dec_ref(v___y_5059_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5064_, lean_object* v_fvarId_5065_, uint8_t v_failIfUnchanged_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___f_5074_; lean_object* v___x_5075_; 
v___x_5072_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5073_ = lean_box(v_failIfUnchanged_5066_);
lean_inc(v_mvarId_5064_);
v___f_5074_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5074_, 0, v_mvarId_5064_);
lean_closure_set(v___f_5074_, 1, v___x_5072_);
lean_closure_set(v___f_5074_, 2, v_fvarId_5065_);
lean_closure_set(v___f_5074_, 3, v___x_5073_);
v___x_5075_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5064_, v___f_5074_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5076_, lean_object* v_fvarId_5077_, lean_object* v_failIfUnchanged_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5084_; lean_object* v_res_5085_; 
v_failIfUnchanged_boxed_5084_ = lean_unbox(v_failIfUnchanged_5078_);
v_res_5085_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5076_, v_fvarId_5077_, v_failIfUnchanged_boxed_5084_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
lean_dec(v_a_5082_);
lean_dec_ref(v_a_5081_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
return v_res_5085_;
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
