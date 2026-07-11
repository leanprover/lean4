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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_18_; uint8_t v_onlyGivenNames_19_; uint8_t v___x_20_; 
v___x_18_ = lean_st_ref_get(v_a_16_);
v_onlyGivenNames_19_ = lean_ctor_get_uint8(v_a_15_, 8);
v___x_20_ = lean_bool_not(v_onlyGivenNames_19_);
if (v___x_20_ == 0)
{
lean_object* v_givenNames_21_; uint8_t v___x_22_; uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_givenNames_21_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_givenNames_21_);
lean_dec(v___x_18_);
v___x_22_ = l_List_isEmpty___redArg(v_givenNames_21_);
lean_dec(v_givenNames_21_);
v___x_23_ = lean_bool_not(v___x_22_);
v___x_24_ = lean_box(v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v___x_18_);
v___x_26_ = lean_box(v___x_20_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg___boxed(lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName(lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_32_, v_a_34_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___boxed(lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Meta_ExtractLets_hasNextName(v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg(lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; lean_object* v_givenNames_59_; 
v___x_58_ = lean_st_ref_get(v_a_56_);
v_givenNames_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_givenNames_59_);
if (lean_obj_tag(v_givenNames_59_) == 0)
{
uint8_t v_onlyGivenNames_60_; 
lean_dec(v___x_58_);
v_onlyGivenNames_60_ = lean_ctor_get_uint8(v_a_55_, 8);
if (v_onlyGivenNames_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2));
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_box(0);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
else
{
lean_object* v_decls_65_; lean_object* v_valueMap_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_78_; 
v_decls_65_ = lean_ctor_get(v___x_58_, 1);
v_valueMap_66_ = lean_ctor_get(v___x_58_, 2);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v___x_58_, 0);
lean_dec(v_unused_79_);
v___x_68_ = v___x_58_;
v_isShared_69_ = v_isSharedCheck_78_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_valueMap_66_);
lean_inc(v_decls_65_);
lean_dec(v___x_58_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_78_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_head_70_; lean_object* v_tail_71_; lean_object* v___x_73_; 
v_head_70_ = lean_ctor_get(v_givenNames_59_, 0);
lean_inc(v_head_70_);
v_tail_71_ = lean_ctor_get(v_givenNames_59_, 1);
lean_inc(v_tail_71_);
lean_dec_ref_known(v_givenNames_59_, 2);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v_tail_71_);
v___x_73_ = v___x_68_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_tail_71_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_decls_65_);
lean_ctor_set(v_reuseFailAlloc_77_, 2, v_valueMap_66_);
v___x_73_ = v_reuseFailAlloc_77_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_st_ref_set(v_a_56_, v___x_73_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v_head_70_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___boxed(lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f(lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_84_, v_a_86_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___boxed(lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_ExtractLets_nextName_x3f(v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(lean_object* v_binderName_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_111_; lean_object* v_a_112_; 
v___x_111_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_106_, v_a_107_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
if (lean_obj_tag(v_a_112_) == 1)
{
lean_object* v_val_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_164_; 
v_val_113_ = lean_ctor_get(v_a_112_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_a_112_);
if (v_isSharedCheck_164_ == 0)
{
v___x_115_ = v_a_112_;
v_isShared_116_ = v_isSharedCheck_164_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_val_113_);
lean_dec(v_a_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_164_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; uint8_t v___x_118_; uint8_t v___x_119_; 
v___x_117_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1));
v___x_118_ = lean_name_eq(v_val_113_, v___x_117_);
v___x_119_ = lean_bool_not(v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = l_Lean_Name_isAnonymous(v_binderName_105_);
if (v___x_120_ == 0)
{
uint8_t v_preserveBinderNames_121_; 
v_preserveBinderNames_121_ = lean_ctor_get_uint8(v_a_106_, 9);
if (v_preserveBinderNames_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = l_Lean_Name_hasMacroScopes(v_val_113_);
lean_dec(v_val_113_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec_ref(v___x_111_);
v___x_123_ = l_Lean_Core_mkFreshUserName(v_binderName_105_, v_a_108_, v_a_109_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_134_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_134_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_134_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_134_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v_a_124_);
v___x_129_ = v___x_115_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_133_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_129_);
v___x_131_ = v___x_126_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_del_object(v___x_115_);
v_a_135_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_123_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_123_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_del_object(v___x_115_);
lean_dec(v_binderName_105_);
return v___x_111_;
}
}
else
{
lean_del_object(v___x_115_);
lean_dec(v_val_113_);
lean_dec(v_binderName_105_);
return v___x_111_;
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_val_113_);
lean_dec_ref(v___x_111_);
lean_dec(v_binderName_105_);
v___x_143_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1));
v___x_144_ = l_Lean_Core_mkFreshUserName(v___x_143_, v_a_108_, v_a_109_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_155_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_155_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v_a_145_);
v___x_150_ = v___x_115_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_150_);
v___x_152_ = v___x_147_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_del_object(v___x_115_);
v_a_156_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_144_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_144_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
else
{
lean_del_object(v___x_115_);
lean_dec(v_val_113_);
lean_dec(v_binderName_105_);
return v___x_111_;
}
}
}
else
{
lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_a_112_);
lean_dec(v_binderName_105_);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v___x_111_, 0);
lean_dec(v_unused_173_);
v___x_166_ = v___x_111_;
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
else
{
lean_dec(v___x_111_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___boxed(lean_object* v_binderName_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(lean_object* v_binderName_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_181_, v_a_182_, v_a_184_, v_a_187_, v_a_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___boxed(lean_object* v_binderName_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(v_binderName_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_200_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
else
{
lean_object* v_head_204_; lean_object* v_tail_205_; uint8_t v___x_206_; 
v_head_204_ = lean_ctor_get(v_x_202_, 0);
v_tail_205_ = lean_ctor_get(v_x_202_, 1);
v___x_206_ = lean_expr_eqv(v_a_201_, v_head_204_);
if (v___x_206_ == 0)
{
v_x_202_ = v_tail_205_;
goto _start;
}
else
{
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0___boxed(lean_object* v_a_208_, lean_object* v_x_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v_a_208_, v_x_209_);
lean_dec(v_x_209_);
lean_dec_ref(v_a_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(lean_object* v_fvars_212_, lean_object* v_e_213_){
_start:
{
uint8_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = l_Lean_Expr_hasFVar(v_e_213_);
v___x_215_ = lean_bool_not(v___x_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; lean_object* v_d_218_; lean_object* v_b_219_; 
v___x_216_ = 1;
switch(lean_obj_tag(v_e_213_))
{
case 7:
{
lean_object* v_binderType_222_; lean_object* v_body_223_; 
v_binderType_222_ = lean_ctor_get(v_e_213_, 1);
lean_inc_ref(v_binderType_222_);
v_body_223_ = lean_ctor_get(v_e_213_, 2);
lean_inc_ref(v_body_223_);
lean_dec_ref_known(v_e_213_, 3);
v_d_218_ = v_binderType_222_;
v_b_219_ = v_body_223_;
goto v___jp_217_;
}
case 6:
{
lean_object* v_binderType_224_; lean_object* v_body_225_; 
v_binderType_224_ = lean_ctor_get(v_e_213_, 1);
lean_inc_ref(v_binderType_224_);
v_body_225_ = lean_ctor_get(v_e_213_, 2);
lean_inc_ref(v_body_225_);
lean_dec_ref_known(v_e_213_, 3);
v_d_218_ = v_binderType_224_;
v_b_219_ = v_body_225_;
goto v___jp_217_;
}
case 10:
{
lean_object* v_expr_226_; 
v_expr_226_ = lean_ctor_get(v_e_213_, 1);
lean_inc_ref(v_expr_226_);
lean_dec_ref_known(v_e_213_, 2);
v_e_213_ = v_expr_226_;
goto _start;
}
case 8:
{
lean_object* v_type_228_; lean_object* v_value_229_; lean_object* v_body_230_; uint8_t v___x_231_; 
v_type_228_ = lean_ctor_get(v_e_213_, 1);
lean_inc_ref(v_type_228_);
v_value_229_ = lean_ctor_get(v_e_213_, 2);
lean_inc_ref(v_value_229_);
v_body_230_ = lean_ctor_get(v_e_213_, 3);
lean_inc_ref(v_body_230_);
lean_dec_ref_known(v_e_213_, 4);
v___x_231_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_212_, v_type_228_);
if (v___x_231_ == 0)
{
uint8_t v___x_232_; 
v___x_232_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_212_, v_value_229_);
if (v___x_232_ == 0)
{
v_e_213_ = v_body_230_;
goto _start;
}
else
{
lean_dec_ref(v_body_230_);
return v___x_216_;
}
}
else
{
lean_dec_ref(v_body_230_);
lean_dec_ref(v_value_229_);
return v___x_216_;
}
}
case 5:
{
lean_object* v_fn_234_; lean_object* v_arg_235_; uint8_t v___x_236_; 
v_fn_234_ = lean_ctor_get(v_e_213_, 0);
lean_inc_ref(v_fn_234_);
v_arg_235_ = lean_ctor_get(v_e_213_, 1);
lean_inc_ref(v_arg_235_);
lean_dec_ref_known(v_e_213_, 2);
v___x_236_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_212_, v_fn_234_);
if (v___x_236_ == 0)
{
v_e_213_ = v_arg_235_;
goto _start;
}
else
{
lean_dec_ref(v_arg_235_);
return v___x_216_;
}
}
case 11:
{
lean_object* v_struct_238_; 
v_struct_238_ = lean_ctor_get(v_e_213_, 2);
lean_inc_ref(v_struct_238_);
lean_dec_ref_known(v_e_213_, 3);
v_e_213_ = v_struct_238_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_fvarId_240_ = lean_ctor_get(v_e_213_, 0);
lean_inc(v_fvarId_240_);
lean_dec_ref_known(v_e_213_, 1);
v___x_241_ = l_Lean_Expr_fvar___override(v_fvarId_240_);
v___x_242_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v___x_241_, v_fvars_212_);
lean_dec_ref(v___x_241_);
return v___x_242_;
}
default: 
{
lean_dec_ref(v_e_213_);
return v___x_215_;
}
}
v___jp_217_:
{
uint8_t v___x_220_; 
v___x_220_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_212_, v_d_218_);
if (v___x_220_ == 0)
{
v_e_213_ = v_b_219_;
goto _start;
}
else
{
lean_dec_ref(v_b_219_);
return v___x_216_;
}
}
}
else
{
uint8_t v___x_243_; 
lean_dec_ref(v_e_213_);
v___x_243_ = 0;
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1___boxed(lean_object* v_fvars_244_, lean_object* v_e_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_244_, v_e_245_);
lean_dec(v_fvars_244_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_extractable(lean_object* v_fvars_248_, lean_object* v_e_249_){
_start:
{
uint8_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_248_, v_e_249_);
v___x_251_ = lean_bool_not(v___x_250_);
return v___x_251_;
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
uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_566_ = l_Lean_Expr_hasFVar(v_e_565_);
v___x_567_ = lean_bool_not(v___x_566_);
if (v___x_567_ == 0)
{
uint8_t v___x_568_; lean_object* v_d_570_; lean_object* v_b_571_; 
v___x_568_ = 1;
switch(lean_obj_tag(v_e_565_))
{
case 7:
{
lean_object* v_binderType_574_; lean_object* v_body_575_; 
v_binderType_574_ = lean_ctor_get(v_e_565_, 1);
v_body_575_ = lean_ctor_get(v_e_565_, 2);
v_d_570_ = v_binderType_574_;
v_b_571_ = v_body_575_;
goto v___jp_569_;
}
case 6:
{
lean_object* v_binderType_576_; lean_object* v_body_577_; 
v_binderType_576_ = lean_ctor_get(v_e_565_, 1);
v_body_577_ = lean_ctor_get(v_e_565_, 2);
v_d_570_ = v_binderType_576_;
v_b_571_ = v_body_577_;
goto v___jp_569_;
}
case 10:
{
lean_object* v_expr_578_; 
v_expr_578_ = lean_ctor_get(v_e_565_, 1);
v_e_565_ = v_expr_578_;
goto _start;
}
case 8:
{
lean_object* v_type_580_; lean_object* v_value_581_; lean_object* v_body_582_; uint8_t v___x_583_; 
v_type_580_ = lean_ctor_get(v_e_565_, 1);
v_value_581_ = lean_ctor_get(v_e_565_, 2);
v_body_582_ = lean_ctor_get(v_e_565_, 3);
v___x_583_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_type_580_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_value_581_);
if (v___x_584_ == 0)
{
v_e_565_ = v_body_582_;
goto _start;
}
else
{
return v___x_568_;
}
}
else
{
return v___x_568_;
}
}
case 5:
{
lean_object* v_fn_586_; lean_object* v_arg_587_; uint8_t v___x_588_; 
v_fn_586_ = lean_ctor_get(v_e_565_, 0);
v_arg_587_ = lean_ctor_get(v_e_565_, 1);
v___x_588_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_fn_586_);
if (v___x_588_ == 0)
{
v_e_565_ = v_arg_587_;
goto _start;
}
else
{
return v___x_568_;
}
}
case 11:
{
lean_object* v_struct_590_; 
v_struct_590_ = lean_ctor_get(v_e_565_, 2);
v_e_565_ = v_struct_590_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_592_; uint8_t v___x_593_; 
v_fvarId_592_ = lean_ctor_get(v_e_565_, 0);
v___x_593_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_fvarId_592_, v___x_564_);
return v___x_593_;
}
default: 
{
return v___x_567_;
}
}
v___jp_569_:
{
uint8_t v___x_572_; 
v___x_572_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_564_, v_d_570_);
if (v___x_572_ == 0)
{
v_e_565_ = v_b_571_;
goto _start;
}
else
{
return v___x_568_;
}
}
}
else
{
uint8_t v___x_594_; 
v___x_594_ = 0;
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1___boxed(lean_object* v___x_595_, lean_object* v_e_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_595_, v_e_596_);
lean_dec_ref(v_e_596_);
lean_dec(v___x_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(lean_object* v_as_599_, size_t v_sz_600_, size_t v_i_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_a_605_; uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_lt(v_i_601_, v_sz_600_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_b_602_);
return v___x_610_;
}
else
{
lean_object* v_snd_611_; lean_object* v_fst_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_646_; 
v_snd_611_ = lean_ctor_get(v_b_602_, 1);
v_fst_612_ = lean_ctor_get(v_b_602_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_b_602_);
if (v_isSharedCheck_646_ == 0)
{
v___x_614_ = v_b_602_;
v_isShared_615_ = v_isSharedCheck_646_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_612_);
lean_dec(v_b_602_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_646_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_fst_616_; lean_object* v_snd_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_645_; 
v_fst_616_ = lean_ctor_get(v_snd_611_, 0);
v_snd_617_ = lean_ctor_get(v_snd_611_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_snd_611_);
if (v_isSharedCheck_645_ == 0)
{
v___x_619_ = v_snd_611_;
v_isShared_620_ = v_isSharedCheck_645_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snd_617_);
lean_inc(v_fst_616_);
lean_dec(v_snd_611_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_645_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_a_621_; lean_object* v_decl_622_; uint8_t v___y_624_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_a_621_ = lean_array_uget_borrowed(v_as_599_, v_i_601_);
v_decl_622_ = lean_ctor_get(v_a_621_, 0);
v___x_641_ = l_Lean_LocalDecl_type(v_decl_622_);
v___x_642_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_612_, v___x_641_);
lean_dec_ref(v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = l_Lean_LocalDecl_value(v_decl_622_, v___x_642_);
v___x_644_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_612_, v___x_643_);
lean_dec_ref(v___x_643_);
v___y_624_ = v___x_644_;
goto v___jp_623_;
}
else
{
v___y_624_ = v___x_642_;
goto v___jp_623_;
}
v___jp_623_:
{
if (v___y_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_627_; 
lean_inc(v_a_621_);
v___x_625_ = lean_array_push(v_fst_616_, v_a_621_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_625_);
v___x_627_ = v___x_619_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_snd_617_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_627_);
v___x_629_ = v___x_614_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_fst_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v_a_605_ = v___x_629_;
goto v___jp_604_;
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_inc(v_a_621_);
v___x_632_ = lean_array_push(v_snd_617_, v_a_621_);
v___x_633_ = l_Lean_LocalDecl_fvarId(v_decl_622_);
v___x_634_ = l_Lean_FVarIdSet_insert(v_fst_612_, v___x_633_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_632_);
v___x_636_ = v___x_619_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_fst_616_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_632_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_636_);
lean_ctor_set(v___x_614_, 0, v___x_634_);
v___x_638_ = v___x_614_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v_a_605_ = v___x_638_;
goto v___jp_604_;
}
}
}
}
}
}
}
v___jp_604_:
{
size_t v___x_606_; size_t v___x_607_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_601_, v___x_606_);
v_i_601_ = v___x_607_;
v_b_602_ = v_a_605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(lean_object* v_as_647_, lean_object* v_sz_648_, lean_object* v_i_649_, lean_object* v_b_650_, lean_object* v___y_651_){
_start:
{
size_t v_sz_boxed_652_; size_t v_i_boxed_653_; lean_object* v_res_654_; 
v_sz_boxed_652_ = lean_unbox_usize(v_sz_648_);
lean_dec(v_sz_648_);
v_i_boxed_653_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_647_, v_sz_boxed_652_, v_i_boxed_653_, v_b_650_);
lean_dec_ref(v_as_647_);
return v_res_654_;
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
v___x_670_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
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
lean_object* v_decl_760_; lean_object* v___x_761_; uint8_t v___x_762_; uint8_t v___x_763_; 
v_decl_760_ = lean_ctor_get(v_x2_759_, 0);
v___x_761_ = l_Lean_LocalDecl_fvarId(v_decl_760_);
v___x_762_ = l_Lean_LocalContext_contains(v_lctx_757_, v___x_761_);
lean_dec(v___x_761_);
v___x_763_ = lean_bool_not(v___x_762_);
if (v___x_763_ == 0)
{
lean_dec_ref(v_x2_759_);
return v_x1_758_;
}
else
{
lean_object* v___x_764_; 
v___x_764_ = lean_array_push(v_x1_758_, v_x2_759_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object* v_lctx_765_, lean_object* v_x1_766_, lean_object* v_x2_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(v_lctx_765_, v_x1_766_, v_x2_767_);
lean_dec_ref(v_lctx_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_k_791_, lean_object* v_decls_792_, lean_object* v_lctx_793_){
_start:
{
lean_object* v___y_795_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_array_get_size(v_decls_792_);
v___x_804_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_805_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_806_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_806_ == 0)
{
lean_dec_ref(v_lctx_793_);
lean_dec_ref(v_decls_792_);
v___y_795_ = v___x_804_;
goto v___jp_794_;
}
else
{
lean_object* v___f_807_; uint8_t v___x_808_; 
v___f_807_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_807_, 0, v_lctx_793_);
v___x_808_ = lean_nat_dec_le(v___x_803_, v___x_803_);
if (v___x_808_ == 0)
{
if (v___x_806_ == 0)
{
lean_dec_ref(v___f_807_);
lean_dec_ref(v_decls_792_);
v___y_795_ = v___x_804_;
goto v___jp_794_;
}
else
{
size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((size_t)0ULL);
v___x_810_ = lean_usize_of_nat(v___x_803_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_805_, v___f_807_, v_decls_792_, v___x_809_, v___x_810_, v___x_804_);
v___y_795_ = v___x_811_;
goto v___jp_794_;
}
}
else
{
size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
v___x_812_ = ((size_t)0ULL);
v___x_813_ = lean_usize_of_nat(v___x_803_);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_805_, v___f_807_, v_decls_792_, v___x_812_, v___x_813_, v___x_804_);
v___y_795_ = v___x_814_;
goto v___jp_794_;
}
}
v___jp_794_:
{
lean_object* v___x_796_; size_t v_sz_797_; size_t v___x_798_; lean_object* v_decls_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_796_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_797_ = lean_array_size(v___y_795_);
v___x_798_ = ((size_t)0ULL);
v_decls_799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_796_, v___f_788_, v_sz_797_, v___x_798_, v___y_795_);
v___x_800_ = lean_array_to_list(v_decls_799_);
v___x_801_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_789_, v_inst_790_, v___x_800_, v_k_791_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_decls_819_, lean_object* v_k_820_){
_start:
{
lean_object* v_toBind_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; 
v_toBind_821_ = lean_ctor_get(v_inst_816_, 1);
lean_inc(v_toBind_821_);
v___f_822_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_823_, 0, v___f_822_);
lean_closure_set(v___f_823_, 1, v_inst_817_);
lean_closure_set(v___f_823_, 2, v_inst_816_);
lean_closure_set(v___f_823_, 3, v_k_820_);
lean_closure_set(v___f_823_, 4, v_decls_819_);
v___x_824_ = lean_apply_4(v_toBind_821_, lean_box(0), lean_box(0), v_inst_818_, v___f_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_825_, lean_object* v_00_u03b1_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_decls_830_, lean_object* v_k_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_827_, v_inst_828_, v_inst_829_, v_decls_830_, v_k_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_833_, size_t v_i_834_, size_t v_stop_835_, lean_object* v_b_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = lean_usize_dec_eq(v_i_834_, v_stop_835_);
if (v___x_837_ == 0)
{
size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; lean_object* v_decl_841_; uint8_t v_isLet_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; 
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_sub(v_i_834_, v___x_838_);
v___x_840_ = lean_array_uget_borrowed(v_as_833_, v___x_839_);
v_decl_841_ = lean_ctor_get(v___x_840_, 0);
v_isLet_842_ = lean_ctor_get_uint8(v___x_840_, sizeof(void*)*1);
v___x_843_ = l_Lean_LocalDecl_userName(v_decl_841_);
v___x_844_ = l_Lean_LocalDecl_type(v_decl_841_);
v___x_845_ = l_Lean_LocalDecl_value(v_decl_841_, v___x_837_);
lean_inc_ref(v_decl_841_);
v___x_846_ = l_Lean_LocalDecl_toExpr(v_decl_841_);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_mk_empty_array_with_capacity(v___x_847_);
v___x_849_ = lean_array_push(v___x_848_, v___x_846_);
v___x_850_ = lean_expr_abstract(v_b_836_, v___x_849_);
lean_dec_ref(v___x_849_);
lean_dec_ref(v_b_836_);
v___x_851_ = lean_bool_not(v_isLet_842_);
v___x_852_ = l_Lean_Expr_letE___override(v___x_843_, v___x_844_, v___x_845_, v___x_850_, v___x_851_);
v_i_834_ = v___x_839_;
v_b_836_ = v___x_852_;
goto _start;
}
else
{
return v_b_836_;
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
size_t v_sz_914_; size_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v_sz_914_ = lean_array_size(v_decls_909_);
v___x_915_ = ((size_t)0ULL);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_904_, v_sz_914_, v___x_915_, v_decls_909_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_916_);
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_givenNames_908_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_valueMap_910_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_st_ref_set(v_a_905_, v___x_918_);
v___x_920_ = lean_box(0);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
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
lean_object* v___x_1028_; lean_object* v_decl_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1028_ = lean_array_uget_borrowed(v_as_1018_, v_i_1019_);
v_decl_1029_ = lean_ctor_get(v___x_1028_, 0);
v___x_1030_ = l_Lean_LocalDecl_fvarId(v_decl_1029_);
v___x_1031_ = l_Lean_LocalContext_contains(v___x_1017_, v___x_1030_);
lean_dec(v___x_1030_);
v___x_1032_ = lean_bool_not(v___x_1031_);
if (v___x_1032_ == 0)
{
v___y_1023_ = v_b_1021_;
goto v___jp_1022_;
}
else
{
lean_object* v___x_1033_; 
lean_inc(v___x_1028_);
v___x_1033_ = lean_array_push(v_b_1021_, v___x_1028_);
v___y_1023_ = v___x_1033_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(lean_object* v___x_1034_, lean_object* v_as_1035_, lean_object* v_i_1036_, lean_object* v_stop_1037_, lean_object* v_b_1038_){
_start:
{
size_t v_i_boxed_1039_; size_t v_stop_boxed_1040_; lean_object* v_res_1041_; 
v_i_boxed_1039_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_stop_boxed_1040_ = lean_unbox_usize(v_stop_1037_);
lean_dec(v_stop_1037_);
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_1034_, v_as_1035_, v_i_boxed_1039_, v_stop_boxed_1040_, v_b_1038_);
lean_dec_ref(v_as_1035_);
lean_dec_ref(v___x_1034_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(lean_object* v_decls_1042_, lean_object* v_k_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___y_1053_; lean_object* v_lctx_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_lctx_1059_ = lean_ctor_get(v___y_1047_, 2);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_array_get_size(v_decls_1042_);
v___x_1062_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_1063_ = lean_nat_dec_lt(v___x_1060_, v___x_1061_);
if (v___x_1063_ == 0)
{
v___y_1053_ = v___x_1062_;
goto v___jp_1052_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_nat_dec_le(v___x_1061_, v___x_1061_);
if (v___x_1064_ == 0)
{
if (v___x_1063_ == 0)
{
v___y_1053_ = v___x_1062_;
goto v___jp_1052_;
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1061_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1059_, v_decls_1042_, v___x_1065_, v___x_1066_, v___x_1062_);
v___y_1053_ = v___x_1067_;
goto v___jp_1052_;
}
}
else
{
size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = ((size_t)0ULL);
v___x_1069_ = lean_usize_of_nat(v___x_1061_);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1059_, v_decls_1042_, v___x_1068_, v___x_1069_, v___x_1062_);
v___y_1053_ = v___x_1070_;
goto v___jp_1052_;
}
}
v___jp_1052_:
{
size_t v_sz_1054_; size_t v___x_1055_; lean_object* v_decls_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_sz_1054_ = lean_array_size(v___y_1053_);
v___x_1055_ = ((size_t)0ULL);
v_decls_1056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_1054_, v___x_1055_, v___y_1053_);
v___x_1057_ = lean_array_to_list(v_decls_1056_);
v___x_1058_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v___x_1057_, v_k_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object* v_decls_1071_, lean_object* v_k_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1071_, v_k_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec_ref(v_decls_1071_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_fvarId_1082_, lean_object* v_as_1083_, lean_object* v_j_1084_){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = lean_array_get_size(v_as_1083_);
v___x_1086_ = lean_nat_dec_lt(v_j_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec(v_j_1084_);
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v_decl_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1088_ = lean_array_fget_borrowed(v_as_1083_, v_j_1084_);
v_decl_1089_ = lean_ctor_get(v___x_1088_, 0);
v___x_1090_ = l_Lean_LocalDecl_fvarId(v_decl_1089_);
v___x_1091_ = l_Lean_instBEqFVarId_beq(v___x_1090_, v_fvarId_1082_);
lean_dec(v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_add(v_j_1084_, v___x_1092_);
lean_dec(v_j_1084_);
v_j_1084_ = v___x_1093_;
goto _start;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_j_1084_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_fvarId_1096_, lean_object* v_as_1097_, lean_object* v_j_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1096_, v_as_1097_, v_j_1098_);
lean_dec_ref(v_as_1097_);
lean_dec(v_fvarId_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1100_, lean_object* v_k_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v_lctx_1111_; uint8_t v___x_1112_; 
v___x_1110_ = lean_st_ref_get(v_a_1104_);
v_lctx_1111_ = lean_ctor_get(v_a_1105_, 2);
v___x_1112_ = l_Lean_LocalContext_contains(v_lctx_1111_, v_fvarId_1100_);
if (v___x_1112_ == 0)
{
lean_object* v_decls_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_decls_1113_ = lean_ctor_get(v___x_1110_, 1);
lean_inc_ref(v_decls_1113_);
lean_dec(v___x_1110_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1100_, v_decls_1113_, v___x_1114_);
if (lean_obj_tag(v___x_1115_) == 1)
{
lean_object* v_val_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_val_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_val_1116_, v___x_1117_);
lean_dec(v_val_1116_);
v___x_1119_ = l_Array_toSubarray___redArg(v_decls_1113_, v___x_1114_, v___x_1118_);
v___x_1120_ = l_Subarray_copy___redArg(v___x_1119_);
v___x_1121_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_1120_, v_k_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec_ref(v___x_1120_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
lean_dec(v___x_1115_);
lean_dec_ref(v_decls_1113_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc(v_a_1103_);
lean_inc_ref(v_a_1102_);
v___x_1122_ = lean_apply_8(v_k_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, lean_box(0));
return v___x_1122_;
}
}
else
{
lean_object* v___x_1123_; 
lean_dec(v___x_1110_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc(v_a_1103_);
lean_inc_ref(v_a_1102_);
v___x_1123_ = lean_apply_8(v_k_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, lean_box(0));
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1124_, lean_object* v_k_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1124_, v_k_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_fvarId_1124_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1135_, lean_object* v_fvarId_1136_, lean_object* v_k_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1136_, v_k_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1147_, lean_object* v_fvarId_1148_, lean_object* v_k_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1147_, v_fvarId_1148_, v_k_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_fvarId_1148_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object* v_00_u03b1_1159_, lean_object* v_decls_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1160_, v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_decls_1172_, lean_object* v_x_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_1171_, v_decls_1172_, v_x_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object* v_00_u03b1_1183_, lean_object* v_decls_1184_, lean_object* v_k_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1184_, v_k_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object* v_00_u03b1_1195_, lean_object* v_decls_1196_, lean_object* v_k_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_1195_, v_decls_1196_, v_k_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v_decls_1196_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = l_Lean_Expr_hasMVar(v_e_1207_);
v___x_1211_ = lean_bool_not(v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v_mctx_1213_; lean_object* v___x_1214_; lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1217_; lean_object* v_cache_1218_; lean_object* v_zetaDeltaFVarIds_1219_; lean_object* v_postponed_1220_; lean_object* v_diag_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1230_; 
v___x_1212_ = lean_st_ref_get(v___y_1208_);
v_mctx_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref(v_mctx_1213_);
lean_dec(v___x_1212_);
v___x_1214_ = l_Lean_instantiateMVarsCore(v_mctx_1213_, v_e_1207_);
v_fst_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_fst_1215_);
v_snd_1216_ = lean_ctor_get(v___x_1214_, 1);
lean_inc(v_snd_1216_);
lean_dec_ref(v___x_1214_);
v___x_1217_ = lean_st_ref_take(v___y_1208_);
v_cache_1218_ = lean_ctor_get(v___x_1217_, 1);
v_zetaDeltaFVarIds_1219_ = lean_ctor_get(v___x_1217_, 2);
v_postponed_1220_ = lean_ctor_get(v___x_1217_, 3);
v_diag_1221_ = lean_ctor_get(v___x_1217_, 4);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1231_);
v___x_1223_ = v___x_1217_;
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_diag_1221_);
lean_inc(v_postponed_1220_);
lean_inc(v_zetaDeltaFVarIds_1219_);
lean_inc(v_cache_1218_);
lean_dec(v___x_1217_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v_snd_1216_);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_snd_1216_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_cache_1218_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_zetaDeltaFVarIds_1219_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_postponed_1220_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_diag_1221_);
v___x_1226_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_st_ref_set(v___y_1208_, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_fst_1215_);
return v___x_1228_;
}
}
}
else
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_e_1207_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1233_, v___y_1234_);
lean_dec(v___y_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1237_, v___y_1242_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1257_, size_t v_i_1258_, size_t v_stop_1259_, lean_object* v_b_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_a_1270_; uint8_t v___x_1274_; 
v___x_1274_ = lean_usize_dec_eq(v_i_1258_, v_stop_1259_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_array_uget_borrowed(v_as_1257_, v_i_1258_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_box(0);
v_a_1270_ = v___x_1276_;
goto v___jp_1269_;
}
else
{
lean_object* v_val_1277_; uint8_t v___y_1279_; uint8_t v___x_1307_; 
v_val_1277_ = lean_ctor_get(v___x_1275_, 0);
v___x_1307_ = l_Lean_LocalDecl_isLet(v_val_1277_, v___x_1274_);
if (v___x_1307_ == 0)
{
v___y_1279_ = v___x_1307_;
goto v___jp_1278_;
}
else
{
uint8_t v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1277_);
v___x_1309_ = lean_bool_not(v___x_1308_);
v___y_1279_ = v___x_1309_;
goto v___jp_1278_;
}
v___jp_1278_:
{
if (v___y_1279_ == 0)
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_box(0);
v_a_1270_ = v___x_1280_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = l_Lean_LocalDecl_value(v_val_1277_, v___x_1274_);
v___x_1282_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1281_, v___y_1265_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; lean_object* v_givenNames_1285_; lean_object* v_decls_1286_; lean_object* v_valueMap_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1298_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = lean_st_ref_take(v___y_1263_);
v_givenNames_1285_ = lean_ctor_get(v___x_1284_, 0);
v_decls_1286_ = lean_ctor_get(v___x_1284_, 1);
v_valueMap_1287_ = lean_ctor_get(v___x_1284_, 2);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1289_ = v___x_1284_;
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_valueMap_1287_);
lean_inc(v_decls_1286_);
lean_inc(v_givenNames_1285_);
lean_dec(v___x_1284_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1291_ = l_Lean_LocalDecl_fvarId(v_val_1277_);
v___x_1292_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1287_, v_a_1283_, v___x_1291_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 2, v___x_1292_);
v___x_1294_ = v___x_1289_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_givenNames_1285_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_decls_1286_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_st_ref_set(v___y_1263_, v___x_1294_);
v___x_1296_ = lean_box(0);
v_a_1270_ = v___x_1296_;
goto v___jp_1269_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1299_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1282_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1282_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v_b_1260_);
return v___x_1310_;
}
v___jp_1269_:
{
size_t v___x_1271_; size_t v___x_1272_; 
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_add(v_i_1258_, v___x_1271_);
v_i_1258_ = v___x_1272_;
v_b_1260_ = v_a_1270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1311_, lean_object* v_i_1312_, lean_object* v_stop_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
size_t v_i_boxed_1323_; size_t v_stop_boxed_1324_; lean_object* v_res_1325_; 
v_i_boxed_1323_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_stop_boxed_1324_ = lean_unbox_usize(v_stop_1313_);
lean_dec(v_stop_1313_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1311_, v_i_boxed_1323_, v_stop_boxed_1324_, v_b_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec_ref(v_as_1311_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1326_, size_t v_i_1327_, size_t v_stop_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_a_1339_; uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_eq(v_i_1327_, v_stop_1328_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_array_uget_borrowed(v_as_1326_, v_i_1327_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_box(0);
v_a_1339_ = v___x_1345_;
goto v___jp_1338_;
}
else
{
lean_object* v_val_1346_; uint8_t v___y_1348_; uint8_t v___x_1376_; 
v_val_1346_ = lean_ctor_get(v___x_1344_, 0);
v___x_1376_ = l_Lean_LocalDecl_isLet(v_val_1346_, v___x_1343_);
if (v___x_1376_ == 0)
{
v___y_1348_ = v___x_1376_;
goto v___jp_1347_;
}
else
{
uint8_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1346_);
v___x_1378_ = lean_bool_not(v___x_1377_);
v___y_1348_ = v___x_1378_;
goto v___jp_1347_;
}
v___jp_1347_:
{
if (v___y_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_box(0);
v_a_1339_ = v___x_1349_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = l_Lean_LocalDecl_value(v_val_1346_, v___x_1343_);
v___x_1351_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1350_, v___y_1334_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; lean_object* v_givenNames_1354_; lean_object* v_decls_1355_; lean_object* v_valueMap_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1367_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_st_ref_take(v___y_1332_);
v_givenNames_1354_ = lean_ctor_get(v___x_1353_, 0);
v_decls_1355_ = lean_ctor_get(v___x_1353_, 1);
v_valueMap_1356_ = lean_ctor_get(v___x_1353_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1358_ = v___x_1353_;
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_valueMap_1356_);
lean_inc(v_decls_1355_);
lean_inc(v_givenNames_1354_);
lean_dec(v___x_1353_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1360_ = l_Lean_LocalDecl_fvarId(v_val_1346_);
v___x_1361_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1356_, v_a_1352_, v___x_1360_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 2, v___x_1361_);
v___x_1363_ = v___x_1358_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_givenNames_1354_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_decls_1355_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_st_ref_set(v___y_1332_, v___x_1363_);
v___x_1365_ = lean_box(0);
v_a_1339_ = v___x_1365_;
goto v___jp_1338_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1351_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1351_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_b_1329_);
return v___x_1379_;
}
v___jp_1338_:
{
size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1327_, v___x_1340_);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1326_, v___x_1341_, v_stop_1328_, v_a_1339_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1380_, lean_object* v_i_1381_, lean_object* v_stop_1382_, lean_object* v_b_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
size_t v_i_boxed_1392_; size_t v_stop_boxed_1393_; lean_object* v_res_1394_; 
v_i_boxed_1392_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_stop_boxed_1393_ = lean_unbox_usize(v_stop_1382_);
lean_dec(v_stop_1382_);
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1380_, v_i_boxed_1392_, v_stop_boxed_1393_, v_b_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v_as_1380_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
lean_object* v_cs_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1425_; 
v_cs_1404_ = lean_ctor_get(v_x_1395_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_x_1395_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1406_ = v_x_1395_;
v_isShared_1407_ = v_isSharedCheck_1425_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_cs_1404_);
lean_dec(v_x_1395_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1425_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_array_get_size(v_cs_1404_);
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_nat_dec_lt(v___x_1408_, v___x_1409_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref(v_cs_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1410_);
v___x_1413_ = v___x_1406_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1410_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_nat_dec_le(v___x_1409_, v___x_1409_);
if (v___x_1415_ == 0)
{
if (v___x_1411_ == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref(v_cs_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1410_);
v___x_1417_ = v___x_1406_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1410_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
lean_del_object(v___x_1406_);
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1409_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1404_, v___x_1419_, v___x_1420_, v___x_1410_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec_ref(v_cs_1404_);
return v___x_1421_;
}
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
lean_del_object(v___x_1406_);
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1409_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1404_, v___x_1422_, v___x_1423_, v___x_1410_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec_ref(v_cs_1404_);
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_vs_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1447_; 
v_vs_1426_ = lean_ctor_get(v_x_1395_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1395_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1428_ = v_x_1395_;
v_isShared_1429_ = v_isSharedCheck_1447_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_vs_1426_);
lean_dec(v_x_1395_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1447_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_array_get_size(v_vs_1426_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_nat_dec_lt(v___x_1430_, v___x_1431_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1435_; 
lean_dec_ref(v_vs_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1432_);
v___x_1435_ = v___x_1428_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1432_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_le(v___x_1431_, v___x_1431_);
if (v___x_1437_ == 0)
{
if (v___x_1433_ == 0)
{
lean_object* v___x_1439_; 
lean_dec_ref(v_vs_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1432_);
v___x_1439_ = v___x_1428_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1432_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
else
{
size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; 
lean_del_object(v___x_1428_);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = lean_usize_of_nat(v___x_1431_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1426_, v___x_1441_, v___x_1442_, v___x_1432_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec_ref(v_vs_1426_);
return v___x_1443_;
}
}
else
{
size_t v___x_1444_; size_t v___x_1445_; lean_object* v___x_1446_; 
lean_del_object(v___x_1428_);
v___x_1444_ = ((size_t)0ULL);
v___x_1445_ = lean_usize_of_nat(v___x_1431_);
v___x_1446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1426_, v___x_1444_, v___x_1445_, v___x_1432_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec_ref(v_vs_1426_);
return v___x_1446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1448_, size_t v_i_1449_, size_t v_stop_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_usize_dec_eq(v_i_1449_, v_stop_1450_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_array_uget_borrowed(v_as_1448_, v_i_1449_);
lean_inc(v___x_1461_);
v___x_1462_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1461_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; size_t v___x_1464_; size_t v___x_1465_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1449_, v___x_1464_);
v_i_1449_ = v___x_1465_;
v_b_1451_ = v_a_1463_;
goto _start;
}
else
{
return v___x_1462_;
}
}
else
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_b_1451_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1468_, lean_object* v_i_1469_, lean_object* v_stop_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
size_t v_i_boxed_1480_; size_t v_stop_boxed_1481_; lean_object* v_res_1482_; 
v_i_boxed_1480_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_stop_boxed_1481_ = lean_unbox_usize(v_stop_1470_);
lean_dec(v_stop_1470_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1468_, v_i_boxed_1480_, v_stop_boxed_1481_, v_b_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v_as_1468_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_root_1502_; lean_object* v_tail_1503_; lean_object* v___x_1504_; 
v_root_1502_ = lean_ctor_get(v_t_1493_, 0);
lean_inc_ref(v_root_1502_);
v_tail_1503_ = lean_ctor_get(v_t_1493_, 1);
lean_inc_ref(v_tail_1503_);
lean_dec_ref(v_t_1493_);
v___x_1504_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1502_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1525_; 
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v___x_1504_, 0);
lean_dec(v_unused_1526_);
v___x_1506_ = v___x_1504_;
v_isShared_1507_ = v_isSharedCheck_1525_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v___x_1504_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1525_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_array_get_size(v_tail_1503_);
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_nat_dec_lt(v___x_1508_, v___x_1509_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v_tail_1503_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1510_);
v___x_1513_ = v___x_1506_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1510_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_nat_dec_le(v___x_1509_, v___x_1509_);
if (v___x_1515_ == 0)
{
if (v___x_1511_ == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref(v_tail_1503_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1510_);
v___x_1517_ = v___x_1506_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1510_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
else
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
lean_del_object(v___x_1506_);
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = lean_usize_of_nat(v___x_1509_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1503_, v___x_1519_, v___x_1520_, v___x_1510_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec_ref(v_tail_1503_);
return v___x_1521_;
}
}
else
{
size_t v___x_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
lean_del_object(v___x_1506_);
v___x_1522_ = ((size_t)0ULL);
v___x_1523_ = lean_usize_of_nat(v___x_1509_);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1503_, v___x_1522_, v___x_1523_, v___x_1510_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec_ref(v_tail_1503_);
return v___x_1524_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1503_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1536_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1538_, size_t v_x_1539_, size_t v_x_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
if (lean_obj_tag(v_x_1538_) == 0)
{
lean_object* v_cs_1549_; lean_object* v___x_1550_; size_t v___x_1551_; lean_object* v_j_1552_; lean_object* v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v_cs_1549_ = lean_ctor_get(v_x_1538_, 0);
lean_inc_ref(v_cs_1549_);
lean_dec_ref_known(v_x_1538_, 1);
v___x_1550_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1551_ = lean_usize_shift_right(v_x_1539_, v_x_1540_);
v_j_1552_ = lean_usize_to_nat(v___x_1551_);
v___x_1553_ = lean_array_get_borrowed(v___x_1550_, v_cs_1549_, v_j_1552_);
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_shift_left(v___x_1554_, v_x_1540_);
v___x_1556_ = lean_usize_sub(v___x_1555_, v___x_1554_);
v___x_1557_ = lean_usize_land(v_x_1539_, v___x_1556_);
v___x_1558_ = ((size_t)5ULL);
v___x_1559_ = lean_usize_sub(v_x_1540_, v___x_1558_);
lean_inc(v___x_1553_);
v___x_1560_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1553_, v___x_1557_, v___x_1559_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1582_; 
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1583_);
v___x_1562_ = v___x_1560_;
v_isShared_1563_ = v_isSharedCheck_1582_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v___x_1560_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1582_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_add(v_j_1552_, v___x_1564_);
lean_dec(v_j_1552_);
v___x_1566_ = lean_array_get_size(v_cs_1549_);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_nat_dec_lt(v___x_1565_, v___x_1566_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1570_; 
lean_dec(v___x_1565_);
lean_dec_ref(v_cs_1549_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1567_);
v___x_1570_ = v___x_1562_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1567_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
else
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_le(v___x_1566_, v___x_1566_);
if (v___x_1572_ == 0)
{
if (v___x_1568_ == 0)
{
lean_object* v___x_1574_; 
lean_dec(v___x_1565_);
lean_dec_ref(v_cs_1549_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1567_);
v___x_1574_ = v___x_1562_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1567_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
lean_del_object(v___x_1562_);
v___x_1576_ = lean_usize_of_nat(v___x_1565_);
lean_dec(v___x_1565_);
v___x_1577_ = lean_usize_of_nat(v___x_1566_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1549_, v___x_1576_, v___x_1577_, v___x_1567_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v_cs_1549_);
return v___x_1578_;
}
}
else
{
size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
lean_del_object(v___x_1562_);
v___x_1579_ = lean_usize_of_nat(v___x_1565_);
lean_dec(v___x_1565_);
v___x_1580_ = lean_usize_of_nat(v___x_1566_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1549_, v___x_1579_, v___x_1580_, v___x_1567_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v_cs_1549_);
return v___x_1581_;
}
}
}
}
else
{
lean_dec(v_j_1552_);
lean_dec_ref(v_cs_1549_);
return v___x_1560_;
}
}
else
{
lean_object* v_vs_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1605_; 
v_vs_1584_ = lean_ctor_get(v_x_1538_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1586_ = v_x_1538_;
v_isShared_1587_ = v_isSharedCheck_1605_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_vs_1584_);
lean_dec(v_x_1538_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1605_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1588_ = lean_usize_to_nat(v_x_1539_);
v___x_1589_ = lean_array_get_size(v_vs_1584_);
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_nat_dec_lt(v___x_1588_, v___x_1589_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1593_; 
lean_dec(v___x_1588_);
lean_dec_ref(v_vs_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1590_);
v___x_1593_ = v___x_1586_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1590_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
else
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_nat_dec_le(v___x_1589_, v___x_1589_);
if (v___x_1595_ == 0)
{
if (v___x_1591_ == 0)
{
lean_object* v___x_1597_; 
lean_dec(v___x_1588_);
lean_dec_ref(v_vs_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1590_);
v___x_1597_ = v___x_1586_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1590_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
else
{
size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
lean_del_object(v___x_1586_);
v___x_1599_ = lean_usize_of_nat(v___x_1588_);
lean_dec(v___x_1588_);
v___x_1600_ = lean_usize_of_nat(v___x_1589_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1584_, v___x_1599_, v___x_1600_, v___x_1590_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v_vs_1584_);
return v___x_1601_;
}
}
else
{
size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
lean_del_object(v___x_1586_);
v___x_1602_ = lean_usize_of_nat(v___x_1588_);
lean_dec(v___x_1588_);
v___x_1603_ = lean_usize_of_nat(v___x_1589_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1584_, v___x_1602_, v___x_1603_, v___x_1590_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v_vs_1584_);
return v___x_1604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
size_t v_x_10784__boxed_1617_; size_t v_x_10785__boxed_1618_; lean_object* v_res_1619_; 
v_x_10784__boxed_1617_ = lean_unbox_usize(v_x_1607_);
lean_dec(v_x_1607_);
v_x_10785__boxed_1618_ = lean_unbox_usize(v_x_1608_);
lean_dec(v_x_1608_);
v_res_1619_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1606_, v_x_10784__boxed_1617_, v_x_10785__boxed_1618_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1620_, lean_object* v_start_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_nat_dec_eq(v_start_1621_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v_root_1632_; lean_object* v_tail_1633_; size_t v_shift_1634_; lean_object* v_tailOff_1635_; uint8_t v___x_1636_; 
v_root_1632_ = lean_ctor_get(v_t_1620_, 0);
lean_inc_ref(v_root_1632_);
v_tail_1633_ = lean_ctor_get(v_t_1620_, 1);
lean_inc_ref(v_tail_1633_);
v_shift_1634_ = lean_ctor_get_usize(v_t_1620_, 4);
v_tailOff_1635_ = lean_ctor_get(v_t_1620_, 3);
lean_inc(v_tailOff_1635_);
lean_dec_ref(v_t_1620_);
v___x_1636_ = lean_nat_dec_le(v_tailOff_1635_, v_start_1621_);
if (v___x_1636_ == 0)
{
size_t v___x_1637_; lean_object* v___x_1638_; 
lean_dec(v_tailOff_1635_);
v___x_1637_ = lean_usize_of_nat(v_start_1621_);
v___x_1638_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1632_, v___x_1637_, v_shift_1634_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1658_; 
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1638_, 0);
lean_dec(v_unused_1659_);
v___x_1640_ = v___x_1638_;
v_isShared_1641_ = v_isSharedCheck_1658_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v___x_1638_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1658_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1642_ = lean_array_get_size(v_tail_1633_);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_nat_dec_lt(v___x_1630_, v___x_1642_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v_tail_1633_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1643_);
v___x_1646_ = v___x_1640_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1643_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_le(v___x_1642_, v___x_1642_);
if (v___x_1648_ == 0)
{
if (v___x_1644_ == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref(v_tail_1633_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1643_);
v___x_1650_ = v___x_1640_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1643_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
else
{
size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
lean_del_object(v___x_1640_);
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = lean_usize_of_nat(v___x_1642_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1633_, v___x_1652_, v___x_1653_, v___x_1643_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec_ref(v_tail_1633_);
return v___x_1654_;
}
}
else
{
size_t v___x_1655_; size_t v___x_1656_; lean_object* v___x_1657_; 
lean_del_object(v___x_1640_);
v___x_1655_ = ((size_t)0ULL);
v___x_1656_ = lean_usize_of_nat(v___x_1642_);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1633_, v___x_1655_, v___x_1656_, v___x_1643_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec_ref(v_tail_1633_);
return v___x_1657_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1633_);
return v___x_1638_;
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
lean_dec_ref(v_root_1632_);
v___x_1660_ = lean_nat_sub(v_start_1621_, v_tailOff_1635_);
lean_dec(v_tailOff_1635_);
v___x_1661_ = lean_array_get_size(v_tail_1633_);
v___x_1662_ = lean_box(0);
v___x_1663_ = lean_nat_dec_lt(v___x_1660_, v___x_1661_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
lean_dec(v___x_1660_);
lean_dec_ref(v_tail_1633_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
return v___x_1664_;
}
else
{
uint8_t v___x_1665_; 
v___x_1665_ = lean_nat_dec_le(v___x_1661_, v___x_1661_);
if (v___x_1665_ == 0)
{
if (v___x_1663_ == 0)
{
lean_object* v___x_1666_; 
lean_dec(v___x_1660_);
lean_dec_ref(v_tail_1633_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1662_);
return v___x_1666_;
}
else
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_usize_of_nat(v___x_1660_);
lean_dec(v___x_1660_);
v___x_1668_ = lean_usize_of_nat(v___x_1661_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1633_, v___x_1667_, v___x_1668_, v___x_1662_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec_ref(v_tail_1633_);
return v___x_1669_;
}
}
else
{
size_t v___x_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_usize_of_nat(v___x_1660_);
lean_dec(v___x_1660_);
v___x_1671_ = lean_usize_of_nat(v___x_1661_);
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1633_, v___x_1670_, v___x_1671_, v___x_1662_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec_ref(v_tail_1633_);
return v___x_1672_;
}
}
}
}
else
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1620_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1674_, lean_object* v_start_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1674_, v_start_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v_start_1675_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1685_, lean_object* v_start_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_decls_1695_; lean_object* v___x_1696_; 
v_decls_1695_ = lean_ctor_get(v_lctx_1685_, 1);
lean_inc_ref(v_decls_1695_);
lean_dec_ref(v_lctx_1685_);
v___x_1696_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1695_, v_start_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1697_, lean_object* v_start_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1697_, v_start_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v_start_1698_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_lctx_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_lctx_1716_ = lean_ctor_get(v_a_1711_, 2);
v___x_1717_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1716_);
v___x_1718_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1716_, v___x_1717_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
return v_res_1727_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1729_){
_start:
{
lean_object* v___f_1730_; lean_object* v___x_1731_; 
v___f_1730_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1731_ = lean_find_expr(v___f_1730_, v_e_1729_);
if (lean_obj_tag(v___x_1731_) == 0)
{
uint8_t v___x_1732_; 
v___x_1732_ = 0;
return v___x_1732_;
}
else
{
uint8_t v___x_1733_; 
lean_dec_ref_known(v___x_1731_, 1);
v___x_1733_ = 1;
return v___x_1733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1734_){
_start:
{
uint8_t v_res_1735_; lean_object* v_r_1736_; 
v_res_1735_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1734_);
lean_dec_ref(v_e_1734_);
v_r_1736_ = lean_box(v_res_1735_);
return v_r_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v_b_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
lean_inc(v___y_1745_);
lean_inc_ref(v___y_1744_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1740_);
lean_inc(v___y_1739_);
lean_inc_ref(v___y_1738_);
v___x_1747_ = lean_apply_9(v_k_1737_, v_b_1741_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, lean_box(0));
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v_b_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v_b_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1759_, uint8_t v_bi_1760_, lean_object* v_type_1761_, lean_object* v_k_1762_, uint8_t v_kind_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___f_1772_; lean_object* v___x_1773_; 
lean_inc(v___y_1766_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1772_, 0, v_k_1762_);
lean_closure_set(v___f_1772_, 1, v___y_1764_);
lean_closure_set(v___f_1772_, 2, v___y_1765_);
lean_closure_set(v___f_1772_, 3, v___y_1766_);
v___x_1773_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1759_, v_bi_1760_, v_type_1761_, v___f_1772_, v_kind_1763_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
if (lean_obj_tag(v___x_1773_) == 0)
{
return v___x_1773_;
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_1782_, lean_object* v_bi_1783_, lean_object* v_type_1784_, lean_object* v_k_1785_, lean_object* v_kind_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v_bi_boxed_1795_; uint8_t v_kind_boxed_1796_; lean_object* v_res_1797_; 
v_bi_boxed_1795_ = lean_unbox(v_bi_1783_);
v_kind_boxed_1796_ = lean_unbox(v_kind_1786_);
v_res_1797_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1782_, v_bi_boxed_1795_, v_type_1784_, v_k_1785_, v_kind_boxed_1796_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_1798_, lean_object* v_name_1799_, uint8_t v_bi_1800_, lean_object* v_type_1801_, lean_object* v_k_1802_, uint8_t v_kind_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_1799_, v_bi_1800_, v_type_1801_, v_k_1802_, v_kind_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_1813_, lean_object* v_name_1814_, lean_object* v_bi_1815_, lean_object* v_type_1816_, lean_object* v_k_1817_, lean_object* v_kind_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v_bi_boxed_1827_; uint8_t v_kind_boxed_1828_; lean_object* v_res_1829_; 
v_bi_boxed_1827_ = lean_unbox(v_bi_1815_);
v_kind_boxed_1828_ = lean_unbox(v_kind_1818_);
v_res_1829_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_1813_, v_name_1814_, v_bi_boxed_1827_, v_type_1816_, v_k_1817_, v_kind_boxed_1828_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1830_, lean_object* v___f_1831_, lean_object* v_e_1832_, lean_object* v_____r_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_bool_not(v_types_1830_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v_e_1832_);
v___x_1843_ = lean_box(0);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
v___x_1844_ = lean_apply_9(v___f_1831_, v___x_1843_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, lean_box(0));
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; 
lean_inc_ref(v_e_1832_);
v___x_1845_ = l_Lean_Meta_isType(v_e_1832_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1856_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_unbox(v_a_1846_);
lean_dec(v_a_1846_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_del_object(v___x_1848_);
lean_dec_ref(v_e_1832_);
v___x_1851_ = lean_box(0);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
v___x_1852_ = lean_apply_9(v___f_1831_, v___x_1851_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, lean_box(0));
return v___x_1852_;
}
else
{
lean_object* v___x_1854_; 
lean_dec_ref(v___f_1831_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v_e_1832_);
v___x_1854_ = v___x_1848_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_e_1832_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_e_1832_);
lean_dec_ref(v___f_1831_);
v_a_1857_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1845_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1845_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_1865_, lean_object* v___f_1866_, lean_object* v_e_1867_, lean_object* v_____r_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v_types_boxed_1877_; lean_object* v_res_1878_; 
v_types_boxed_1877_ = lean_unbox(v_types_1865_);
v_res_1878_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_1877_, v___f_1866_, v_e_1867_, v_____r_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1878_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(uint8_t v___y_1879_, uint8_t v___y_1880_){
_start:
{
if (v___y_1879_ == 0)
{
if (v___y_1880_ == 0)
{
uint8_t v___x_1881_; 
v___x_1881_ = 1;
return v___x_1881_;
}
else
{
return v___y_1879_;
}
}
else
{
return v___y_1880_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
uint8_t v___y_49525__boxed_1884_; uint8_t v___y_49526__boxed_1885_; uint8_t v_res_1886_; lean_object* v_r_1887_; 
v___y_49525__boxed_1884_ = lean_unbox(v___y_1882_);
v___y_49526__boxed_1885_ = lean_unbox(v___y_1883_);
v_res_1886_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(v___y_49525__boxed_1884_, v___y_49526__boxed_1885_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_instMonadEIO(lean_box(0));
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_toApplicative_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1979_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1907_ = l_StateRefT_x27_instMonad___redArg(v___x_1906_);
v_toApplicative_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___x_1907_, 1);
lean_dec(v_unused_1980_);
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1979_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_toApplicative_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1979_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_toFunctor_1912_; lean_object* v_toSeq_1913_; lean_object* v_toSeqLeft_1914_; lean_object* v_toSeqRight_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1977_; 
v_toFunctor_1912_ = lean_ctor_get(v_toApplicative_1908_, 0);
v_toSeq_1913_ = lean_ctor_get(v_toApplicative_1908_, 2);
v_toSeqLeft_1914_ = lean_ctor_get(v_toApplicative_1908_, 3);
v_toSeqRight_1915_ = lean_ctor_get(v_toApplicative_1908_, 4);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_toApplicative_1908_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_toApplicative_1908_, 1);
lean_dec(v_unused_1978_);
v___x_1917_ = v_toApplicative_1908_;
v_isShared_1918_ = v_isSharedCheck_1977_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_toSeqRight_1915_);
lean_inc(v_toSeqLeft_1914_);
lean_inc(v_toSeq_1913_);
lean_inc(v_toFunctor_1912_);
lean_dec(v_toApplicative_1908_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1977_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___f_1919_; lean_object* v___f_1920_; lean_object* v___f_1921_; lean_object* v___f_1922_; lean_object* v___x_1923_; lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___f_1926_; lean_object* v___x_1928_; 
v___f_1919_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1920_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1912_);
v___f_1921_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1921_, 0, v_toFunctor_1912_);
v___f_1922_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1922_, 0, v_toFunctor_1912_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___f_1921_);
lean_ctor_set(v___x_1923_, 1, v___f_1922_);
v___f_1924_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1924_, 0, v_toSeqRight_1915_);
v___f_1925_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1925_, 0, v_toSeqLeft_1914_);
v___f_1926_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1926_, 0, v_toSeq_1913_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 4, v___f_1924_);
lean_ctor_set(v___x_1917_, 3, v___f_1925_);
lean_ctor_set(v___x_1917_, 2, v___f_1926_);
lean_ctor_set(v___x_1917_, 1, v___f_1919_);
lean_ctor_set(v___x_1917_, 0, v___x_1923_);
v___x_1928_ = v___x_1917_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___f_1919_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v___f_1926_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v___f_1925_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v___f_1924_);
v___x_1928_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1930_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v___f_1920_);
lean_ctor_set(v___x_1910_, 0, v___x_1928_);
v___x_1930_ = v___x_1910_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___f_1920_);
v___x_1930_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; lean_object* v_toApplicative_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1973_; 
v___x_1931_ = l_StateRefT_x27_instMonad___redArg(v___x_1930_);
v_toApplicative_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1931_, 1);
lean_dec(v_unused_1974_);
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1973_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_toApplicative_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1973_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_toFunctor_1936_; lean_object* v_toSeq_1937_; lean_object* v_toSeqLeft_1938_; lean_object* v_toSeqRight_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1971_; 
v_toFunctor_1936_ = lean_ctor_get(v_toApplicative_1932_, 0);
v_toSeq_1937_ = lean_ctor_get(v_toApplicative_1932_, 2);
v_toSeqLeft_1938_ = lean_ctor_get(v_toApplicative_1932_, 3);
v_toSeqRight_1939_ = lean_ctor_get(v_toApplicative_1932_, 4);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_toApplicative_1932_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v_toApplicative_1932_, 1);
lean_dec(v_unused_1972_);
v___x_1941_ = v_toApplicative_1932_;
v_isShared_1942_ = v_isSharedCheck_1971_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_toSeqRight_1939_);
lean_inc(v_toSeqLeft_1938_);
lean_inc(v_toSeq_1937_);
lean_inc(v_toFunctor_1936_);
lean_dec(v_toApplicative_1932_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1971_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; lean_object* v___f_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___x_1959_; 
v___f_1943_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed), 2, 0);
v___f_1944_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1944_, 0, v___f_1943_);
v___x_1945_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1946_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1946_, 0, v___f_1944_);
lean_closure_set(v___f_1946_, 1, v___x_1945_);
v___f_1947_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
v___x_1948_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5));
v___f_1949_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1949_, 0, v___f_1947_);
lean_closure_set(v___f_1949_, 1, v___x_1948_);
v___f_1950_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6));
v___f_1951_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7));
lean_inc_ref(v_toFunctor_1936_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toFunctor_1936_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toFunctor_1936_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___f_1952_);
lean_ctor_set(v___x_1954_, 1, v___f_1953_);
v___f_1955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1955_, 0, v_toSeqRight_1939_);
v___f_1956_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1956_, 0, v_toSeqLeft_1938_);
v___f_1957_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1957_, 0, v_toSeq_1937_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 4, v___f_1955_);
lean_ctor_set(v___x_1941_, 3, v___f_1956_);
lean_ctor_set(v___x_1941_, 2, v___f_1957_);
lean_ctor_set(v___x_1941_, 1, v___f_1950_);
lean_ctor_set(v___x_1941_, 0, v___x_1954_);
v___x_1959_ = v___x_1941_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___f_1950_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v___f_1957_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v___f_1956_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v___f_1955_);
v___x_1959_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v___f_1951_);
lean_ctor_set(v___x_1934_, 0, v___x_1959_);
v___x_1961_ = v___x_1934_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v___f_1951_);
v___x_1961_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___f_1966_; lean_object* v___x_46422__overap_1967_; lean_object* v___x_1968_; 
v___x_1962_ = l_StateRefT_x27_instMonad___redArg(v___x_1961_);
v___x_1963_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_1905_, v___f_1946_, v___f_1949_, v___x_1962_);
v___x_1964_ = l_Lean_instInhabitedExpr;
v___x_1965_ = l_instInhabitedOfMonad___redArg(v___x_1963_, v___x_1964_);
v___f_1966_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1966_, 0, v___x_1965_);
v___x_46422__overap_1967_ = lean_panic_fn_borrowed(v___f_1966_, v_msg_1896_);
lean_dec_ref(v___f_1966_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1900_);
lean_inc(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
v___x_1968_ = lean_apply_8(v___x_46422__overap_1967_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, lean_box(0));
return v___x_1968_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderName_1991_, uint8_t v_binderInfo_1992_, lean_object* v_e_1993_, lean_object* v_binderType_1994_, lean_object* v_body_1995_, lean_object* v_t_1996_, lean_object* v_b_1997_){
_start:
{
uint8_t v___y_1999_; size_t v___x_2003_; size_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = lean_ptr_addr(v_binderType_1994_);
v___x_2004_ = lean_ptr_addr(v_t_1996_);
v___x_2005_ = lean_usize_dec_eq(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
v___y_1999_ = v___x_2005_;
goto v___jp_1998_;
}
else
{
size_t v___x_2006_; size_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2006_ = lean_ptr_addr(v_body_1995_);
v___x_2007_ = lean_ptr_addr(v_b_1997_);
v___x_2008_ = lean_usize_dec_eq(v___x_2006_, v___x_2007_);
v___y_1999_ = v___x_2008_;
goto v___jp_1998_;
}
v___jp_1998_:
{
if (v___y_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Expr_lam___override(v_binderName_1991_, v_t_1996_, v_b_1997_, v_binderInfo_1992_);
return v___x_2000_;
}
else
{
uint8_t v___x_2001_; 
v___x_2001_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1992_, v_binderInfo_1992_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Expr_lam___override(v_binderName_1991_, v_t_1996_, v_b_1997_, v_binderInfo_1992_);
return v___x_2002_;
}
else
{
lean_dec_ref(v_b_1997_);
lean_dec_ref(v_t_1996_);
lean_dec(v_binderName_1991_);
lean_inc_ref(v_e_1993_);
return v_e_1993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderName_2009_, lean_object* v_binderInfo_2010_, lean_object* v_e_2011_, lean_object* v_binderType_2012_, lean_object* v_body_2013_, lean_object* v_t_2014_, lean_object* v_b_2015_){
_start:
{
uint8_t v_binderInfo_49712__boxed_2016_; lean_object* v_res_2017_; 
v_binderInfo_49712__boxed_2016_ = lean_unbox(v_binderInfo_2010_);
v_res_2017_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderName_2009_, v_binderInfo_49712__boxed_2016_, v_e_2011_, v_binderType_2012_, v_body_2013_, v_t_2014_, v_b_2015_);
lean_dec_ref(v_body_2013_);
lean_dec_ref(v_binderType_2012_);
lean_dec_ref(v_e_2011_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderName_2018_, uint8_t v_binderInfo_2019_, lean_object* v_e_2020_, lean_object* v_binderType_2021_, lean_object* v_body_2022_, lean_object* v_t_2023_, lean_object* v_b_2024_){
_start:
{
uint8_t v___y_2026_; size_t v___x_2030_; size_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = lean_ptr_addr(v_binderType_2021_);
v___x_2031_ = lean_ptr_addr(v_t_2023_);
v___x_2032_ = lean_usize_dec_eq(v___x_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
v___y_2026_ = v___x_2032_;
goto v___jp_2025_;
}
else
{
size_t v___x_2033_; size_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_ptr_addr(v_body_2022_);
v___x_2034_ = lean_ptr_addr(v_b_2024_);
v___x_2035_ = lean_usize_dec_eq(v___x_2033_, v___x_2034_);
v___y_2026_ = v___x_2035_;
goto v___jp_2025_;
}
v___jp_2025_:
{
if (v___y_2026_ == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_Expr_forallE___override(v_binderName_2018_, v_t_2023_, v_b_2024_, v_binderInfo_2019_);
return v___x_2027_;
}
else
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2019_, v_binderInfo_2019_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Expr_forallE___override(v_binderName_2018_, v_t_2023_, v_b_2024_, v_binderInfo_2019_);
return v___x_2029_;
}
else
{
lean_dec_ref(v_b_2024_);
lean_dec_ref(v_t_2023_);
lean_dec(v_binderName_2018_);
lean_inc_ref(v_e_2020_);
return v_e_2020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderName_2036_, lean_object* v_binderInfo_2037_, lean_object* v_e_2038_, lean_object* v_binderType_2039_, lean_object* v_body_2040_, lean_object* v_t_2041_, lean_object* v_b_2042_){
_start:
{
uint8_t v_binderInfo_49746__boxed_2043_; lean_object* v_res_2044_; 
v_binderInfo_49746__boxed_2043_ = lean_unbox(v_binderInfo_2037_);
v_res_2044_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderName_2036_, v_binderInfo_49746__boxed_2043_, v_e_2038_, v_binderType_2039_, v_body_2040_, v_t_2041_, v_b_2042_);
lean_dec_ref(v_body_2040_);
lean_dec_ref(v_binderType_2039_);
lean_dec_ref(v_e_2038_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_2045_, lean_object* v_type_2046_, lean_object* v_val_2047_, lean_object* v_k_2048_, uint8_t v_nondep_2049_, uint8_t v_kind_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___f_2059_; lean_object* v___x_2060_; 
lean_inc(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc_ref(v___y_2051_);
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2059_, 0, v_k_2048_);
lean_closure_set(v___f_2059_, 1, v___y_2051_);
lean_closure_set(v___f_2059_, 2, v___y_2052_);
lean_closure_set(v___f_2059_, 3, v___y_2053_);
v___x_2060_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2045_, v_type_2046_, v_val_2047_, v___f_2059_, v_nondep_2049_, v_kind_2050_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2060_) == 0)
{
return v___x_2060_;
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2069_, lean_object* v_type_2070_, lean_object* v_val_2071_, lean_object* v_k_2072_, lean_object* v_nondep_2073_, lean_object* v_kind_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v_nondep_boxed_2083_; uint8_t v_kind_boxed_2084_; lean_object* v_res_2085_; 
v_nondep_boxed_2083_ = lean_unbox(v_nondep_2073_);
v_kind_boxed_2084_ = lean_unbox(v_kind_2074_);
v_res_2085_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2069_, v_type_2070_, v_val_2071_, v_k_2072_, v_nondep_boxed_2083_, v_kind_boxed_2084_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = l_Lean_instInhabitedExpr;
v___x_2088_ = lean_panic_fn_borrowed(v___x_2087_, v_msg_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2089_, lean_object* v_x_2090_){
_start:
{
if (lean_obj_tag(v_x_2090_) == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_box(0);
return v___x_2091_;
}
else
{
lean_object* v_key_2092_; lean_object* v_value_2093_; lean_object* v_tail_2094_; uint8_t v___x_2095_; 
v_key_2092_ = lean_ctor_get(v_x_2090_, 0);
v_value_2093_ = lean_ctor_get(v_x_2090_, 1);
v_tail_2094_ = lean_ctor_get(v_x_2090_, 2);
v___x_2095_ = l_Lean_ExprStructEq_beq(v_key_2092_, v_a_2089_);
if (v___x_2095_ == 0)
{
v_x_2090_ = v_tail_2094_;
goto _start;
}
else
{
lean_object* v___x_2097_; 
lean_inc(v_value_2093_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_value_2093_);
return v___x_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2098_, v_x_2099_);
lean_dec(v_x_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_buckets_2103_; lean_object* v___x_2104_; uint64_t v___x_2105_; uint64_t v___x_2106_; uint64_t v___x_2107_; uint64_t v_fold_2108_; uint64_t v___x_2109_; uint64_t v___x_2110_; uint64_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_buckets_2103_ = lean_ctor_get(v_m_2101_, 1);
v___x_2104_ = lean_array_get_size(v_buckets_2103_);
v___x_2105_ = l_Lean_ExprStructEq_hash(v_a_2102_);
v___x_2106_ = 32ULL;
v___x_2107_ = lean_uint64_shift_right(v___x_2105_, v___x_2106_);
v_fold_2108_ = lean_uint64_xor(v___x_2105_, v___x_2107_);
v___x_2109_ = 16ULL;
v___x_2110_ = lean_uint64_shift_right(v_fold_2108_, v___x_2109_);
v___x_2111_ = lean_uint64_xor(v_fold_2108_, v___x_2110_);
v___x_2112_ = lean_uint64_to_usize(v___x_2111_);
v___x_2113_ = lean_usize_of_nat(v___x_2104_);
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_sub(v___x_2113_, v___x_2114_);
v___x_2116_ = lean_usize_land(v___x_2112_, v___x_2115_);
v___x_2117_ = lean_array_uget_borrowed(v_buckets_2103_, v___x_2116_);
v___x_2118_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2102_, v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2119_, v_a_2120_);
lean_dec_ref(v_a_2120_);
lean_dec_ref(v_m_2119_);
return v_res_2121_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2122_, lean_object* v_x_2123_){
_start:
{
if (lean_obj_tag(v_x_2123_) == 0)
{
uint8_t v___x_2124_; 
v___x_2124_ = 0;
return v___x_2124_;
}
else
{
lean_object* v_key_2125_; lean_object* v_tail_2126_; lean_object* v_fst_2127_; lean_object* v_snd_2128_; lean_object* v_fst_2129_; lean_object* v_snd_2130_; uint8_t v___x_2134_; 
v_key_2125_ = lean_ctor_get(v_x_2123_, 0);
v_tail_2126_ = lean_ctor_get(v_x_2123_, 2);
v_fst_2127_ = lean_ctor_get(v_key_2125_, 0);
v_snd_2128_ = lean_ctor_get(v_key_2125_, 1);
v_fst_2129_ = lean_ctor_get(v_a_2122_, 0);
v_snd_2130_ = lean_ctor_get(v_a_2122_, 1);
v___x_2134_ = lean_unbox(v_fst_2127_);
if (v___x_2134_ == 0)
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_unbox(v_fst_2129_);
if (v___x_2135_ == 0)
{
goto v___jp_2131_;
}
else
{
v_x_2123_ = v_tail_2126_;
goto _start;
}
}
else
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_unbox(v_fst_2129_);
if (v___x_2137_ == 0)
{
v_x_2123_ = v_tail_2126_;
goto _start;
}
else
{
goto v___jp_2131_;
}
}
v___jp_2131_:
{
uint8_t v___x_2132_; 
v___x_2132_ = l_Lean_ExprStructEq_beq(v_snd_2128_, v_snd_2130_);
if (v___x_2132_ == 0)
{
v_x_2123_ = v_tail_2126_;
goto _start;
}
else
{
return v___x_2132_;
}
}
}
}
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
v___x_2164_ = lean_unbox(v_fst_2157_);
if (v___x_2164_ == 0)
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_unbox(v_fst_2159_);
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
v___x_2166_ = lean_unbox(v_fst_2159_);
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
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_nbuckets_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2217_ = lean_array_get_size(v_data_2216_);
v___x_2218_ = lean_unsigned_to_nat(2u);
v_nbuckets_2219_ = lean_nat_mul(v___x_2217_, v___x_2218_);
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_mk_array(v_nbuckets_2219_, v___x_2221_);
v___x_2223_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2220_, v_data_2216_, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2224_, lean_object* v_a_2225_, lean_object* v_b_2226_){
_start:
{
lean_object* v_size_2227_; lean_object* v_buckets_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2279_; 
v_size_2227_ = lean_ctor_get(v_m_2224_, 0);
v_buckets_2228_ = lean_ctor_get(v_m_2224_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_m_2224_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2230_ = v_m_2224_;
v_isShared_2231_ = v_isSharedCheck_2279_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_buckets_2228_);
lean_inc(v_size_2227_);
lean_dec(v_m_2224_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2279_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_fst_2232_; lean_object* v_snd_2233_; lean_object* v___x_2234_; uint64_t v___y_2236_; uint8_t v___x_2276_; 
v_fst_2232_ = lean_ctor_get(v_a_2225_, 0);
v_snd_2233_ = lean_ctor_get(v_a_2225_, 1);
v___x_2234_ = lean_array_get_size(v_buckets_2228_);
v___x_2276_ = lean_unbox(v_fst_2232_);
if (v___x_2276_ == 0)
{
uint64_t v___x_2277_; 
v___x_2277_ = 13ULL;
v___y_2236_ = v___x_2277_;
goto v___jp_2235_;
}
else
{
uint64_t v___x_2278_; 
v___x_2278_ = 11ULL;
v___y_2236_ = v___x_2278_;
goto v___jp_2235_;
}
v___jp_2235_:
{
uint64_t v___x_2237_; uint64_t v___x_2238_; uint64_t v___x_2239_; uint64_t v___x_2240_; uint64_t v_fold_2241_; uint64_t v___x_2242_; uint64_t v___x_2243_; uint64_t v___x_2244_; size_t v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; lean_object* v_bkt_2250_; uint8_t v___x_2251_; 
v___x_2237_ = l_Lean_ExprStructEq_hash(v_snd_2233_);
v___x_2238_ = lean_uint64_mix_hash(v___y_2236_, v___x_2237_);
v___x_2239_ = 32ULL;
v___x_2240_ = lean_uint64_shift_right(v___x_2238_, v___x_2239_);
v_fold_2241_ = lean_uint64_xor(v___x_2238_, v___x_2240_);
v___x_2242_ = 16ULL;
v___x_2243_ = lean_uint64_shift_right(v_fold_2241_, v___x_2242_);
v___x_2244_ = lean_uint64_xor(v_fold_2241_, v___x_2243_);
v___x_2245_ = lean_uint64_to_usize(v___x_2244_);
v___x_2246_ = lean_usize_of_nat(v___x_2234_);
v___x_2247_ = ((size_t)1ULL);
v___x_2248_ = lean_usize_sub(v___x_2246_, v___x_2247_);
v___x_2249_ = lean_usize_land(v___x_2245_, v___x_2248_);
v_bkt_2250_ = lean_array_uget_borrowed(v_buckets_2228_, v___x_2249_);
v___x_2251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2225_, v_bkt_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v_size_x27_2253_; lean_object* v___x_2254_; lean_object* v_buckets_x27_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2252_ = lean_unsigned_to_nat(1u);
v_size_x27_2253_ = lean_nat_add(v_size_2227_, v___x_2252_);
lean_dec(v_size_2227_);
lean_inc(v_bkt_2250_);
v___x_2254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2254_, 0, v_a_2225_);
lean_ctor_set(v___x_2254_, 1, v_b_2226_);
lean_ctor_set(v___x_2254_, 2, v_bkt_2250_);
v_buckets_x27_2255_ = lean_array_uset(v_buckets_2228_, v___x_2249_, v___x_2254_);
v___x_2256_ = lean_unsigned_to_nat(4u);
v___x_2257_ = lean_nat_mul(v_size_x27_2253_, v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(3u);
v___x_2259_ = lean_nat_div(v___x_2257_, v___x_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_array_get_size(v_buckets_x27_2255_);
v___x_2261_ = lean_nat_dec_le(v___x_2259_, v___x_2260_);
lean_dec(v___x_2259_);
if (v___x_2261_ == 0)
{
lean_object* v_val_2262_; lean_object* v___x_2264_; 
v_val_2262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2255_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v_val_2262_);
lean_ctor_set(v___x_2230_, 0, v_size_x27_2253_);
v___x_2264_ = v___x_2230_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_size_x27_2253_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_val_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_object* v___x_2267_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v_buckets_x27_2255_);
lean_ctor_set(v___x_2230_, 0, v_size_x27_2253_);
v___x_2267_ = v___x_2230_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_size_x27_2253_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_buckets_x27_2255_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
else
{
lean_object* v___x_2269_; lean_object* v_buckets_x27_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_inc(v_bkt_2250_);
v___x_2269_ = lean_box(0);
v_buckets_x27_2270_ = lean_array_uset(v_buckets_2228_, v___x_2249_, v___x_2269_);
v___x_2271_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2225_, v_b_2226_, v_bkt_2250_);
v___x_2272_ = lean_array_uset(v_buckets_x27_2270_, v___x_2249_, v___x_2271_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v___x_2272_);
v___x_2274_ = v___x_2230_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_size_2227_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2280_, lean_object* v_x_2281_){
_start:
{
if (lean_obj_tag(v_x_2281_) == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_box(0);
return v___x_2282_;
}
else
{
lean_object* v_key_2283_; lean_object* v_value_2284_; lean_object* v_tail_2285_; lean_object* v_fst_2286_; lean_object* v_snd_2287_; lean_object* v_fst_2288_; lean_object* v_snd_2289_; uint8_t v___x_2294_; 
v_key_2283_ = lean_ctor_get(v_x_2281_, 0);
v_value_2284_ = lean_ctor_get(v_x_2281_, 1);
v_tail_2285_ = lean_ctor_get(v_x_2281_, 2);
v_fst_2286_ = lean_ctor_get(v_key_2283_, 0);
v_snd_2287_ = lean_ctor_get(v_key_2283_, 1);
v_fst_2288_ = lean_ctor_get(v_a_2280_, 0);
v_snd_2289_ = lean_ctor_get(v_a_2280_, 1);
v___x_2294_ = lean_unbox(v_fst_2286_);
if (v___x_2294_ == 0)
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_unbox(v_fst_2288_);
if (v___x_2295_ == 0)
{
goto v___jp_2290_;
}
else
{
v_x_2281_ = v_tail_2285_;
goto _start;
}
}
else
{
uint8_t v___x_2297_; 
v___x_2297_ = lean_unbox(v_fst_2288_);
if (v___x_2297_ == 0)
{
v_x_2281_ = v_tail_2285_;
goto _start;
}
else
{
goto v___jp_2290_;
}
}
v___jp_2290_:
{
uint8_t v___x_2291_; 
v___x_2291_ = l_Lean_ExprStructEq_beq(v_snd_2287_, v_snd_2289_);
if (v___x_2291_ == 0)
{
v_x_2281_ = v_tail_2285_;
goto _start;
}
else
{
lean_object* v___x_2293_; 
lean_inc(v_value_2284_);
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_value_2284_);
return v___x_2293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2299_, lean_object* v_x_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2299_, v_x_2300_);
lean_dec(v_x_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_buckets_2304_; lean_object* v_fst_2305_; lean_object* v_snd_2306_; lean_object* v___x_2307_; uint64_t v___y_2309_; uint8_t v___x_2325_; 
v_buckets_2304_ = lean_ctor_get(v_m_2302_, 1);
v_fst_2305_ = lean_ctor_get(v_a_2303_, 0);
v_snd_2306_ = lean_ctor_get(v_a_2303_, 1);
v___x_2307_ = lean_array_get_size(v_buckets_2304_);
v___x_2325_ = lean_unbox(v_fst_2305_);
if (v___x_2325_ == 0)
{
uint64_t v___x_2326_; 
v___x_2326_ = 13ULL;
v___y_2309_ = v___x_2326_;
goto v___jp_2308_;
}
else
{
uint64_t v___x_2327_; 
v___x_2327_ = 11ULL;
v___y_2309_ = v___x_2327_;
goto v___jp_2308_;
}
v___jp_2308_:
{
uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v_fold_2314_; uint64_t v___x_2315_; uint64_t v___x_2316_; uint64_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2310_ = l_Lean_ExprStructEq_hash(v_snd_2306_);
v___x_2311_ = lean_uint64_mix_hash(v___y_2309_, v___x_2310_);
v___x_2312_ = 32ULL;
v___x_2313_ = lean_uint64_shift_right(v___x_2311_, v___x_2312_);
v_fold_2314_ = lean_uint64_xor(v___x_2311_, v___x_2313_);
v___x_2315_ = 16ULL;
v___x_2316_ = lean_uint64_shift_right(v_fold_2314_, v___x_2315_);
v___x_2317_ = lean_uint64_xor(v_fold_2314_, v___x_2316_);
v___x_2318_ = lean_uint64_to_usize(v___x_2317_);
v___x_2319_ = lean_usize_of_nat(v___x_2307_);
v___x_2320_ = ((size_t)1ULL);
v___x_2321_ = lean_usize_sub(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_usize_land(v___x_2318_, v___x_2321_);
v___x_2323_ = lean_array_uget_borrowed(v_buckets_2304_, v___x_2322_);
v___x_2324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2303_, v___x_2323_);
return v___x_2324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2328_, v_a_2329_);
lean_dec_ref(v_a_2329_);
lean_dec_ref(v_m_2328_);
return v_res_2330_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2331_; lean_object* v_dummy_2332_; 
v___x_2331_ = lean_box(0);
v_dummy_2332_ = l_Lean_Expr_sort___override(v___x_2331_);
return v_dummy_2332_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2333_, lean_object* v_fst_2334_, lean_object* v_fvars_2335_, lean_object* v_a_2336_, lean_object* v_b_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_a_2347_; uint8_t v___x_2351_; 
v___x_2351_ = lean_nat_dec_lt(v_a_2336_, v_upperBound_2333_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_dec(v_a_2336_);
lean_dec(v_fvars_2335_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_b_2337_);
return v___x_2352_;
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v_binderInfo_2355_; uint8_t v___x_2356_; 
v___x_2353_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2354_ = lean_array_get_borrowed(v___x_2353_, v_fst_2334_, v_a_2336_);
v_binderInfo_2355_ = lean_ctor_get_uint8(v___x_2354_, sizeof(void*)*2);
v___x_2356_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2355_);
if (v___x_2356_ == 0)
{
v_a_2347_ = v_b_2337_;
goto v___jp_2346_;
}
else
{
uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2357_ = 0;
v___x_2358_ = l_Lean_instInhabitedExpr;
v___x_2359_ = lean_array_get_borrowed(v___x_2358_, v_b_2337_, v_a_2336_);
lean_inc(v___x_2359_);
lean_inc(v_fvars_2335_);
v___x_2360_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2335_, v___x_2359_, v___x_2357_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = lean_array_set(v_b_2337_, v_a_2336_, v_a_2361_);
v_a_2347_ = v___x_2362_;
goto v___jp_2346_;
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v_b_2337_);
lean_dec(v_a_2336_);
lean_dec(v_fvars_2335_);
v_a_2363_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2360_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2360_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_nat_add(v_a_2336_, v___x_2348_);
lean_dec(v_a_2336_);
v_a_2336_ = v___x_2349_;
v_b_2337_ = v_a_2347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2371_, size_t v_sz_2372_, size_t v_i_2373_, lean_object* v_bs_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_usize_dec_lt(v_i_2373_, v_sz_2372_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
lean_dec(v_fvars_2371_);
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_bs_2374_);
return v___x_2384_;
}
else
{
uint8_t v___x_2385_; lean_object* v_v_2386_; lean_object* v___x_2387_; 
v___x_2385_ = 0;
v_v_2386_ = lean_array_uget_borrowed(v_bs_2374_, v_i_2373_);
lean_inc(v_v_2386_);
lean_inc(v_fvars_2371_);
v___x_2387_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2371_, v_v_2386_, v___x_2385_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v_bs_x27_2390_; size_t v___x_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = lean_unsigned_to_nat(0u);
v_bs_x27_2390_ = lean_array_uset(v_bs_2374_, v_i_2373_, v___x_2389_);
v___x_2391_ = ((size_t)1ULL);
v___x_2392_ = lean_usize_add(v_i_2373_, v___x_2391_);
v___x_2393_ = lean_array_uset(v_bs_x27_2390_, v_i_2373_, v_a_2388_);
v_i_2373_ = v___x_2392_;
v_bs_2374_ = v___x_2393_;
goto _start;
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec_ref(v_bs_2374_);
lean_dec(v_fvars_2371_);
v_a_2395_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2387_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2387_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2403_, lean_object* v_f_2404_, lean_object* v_args_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
uint8_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = 0;
lean_inc_ref(v_f_2404_);
lean_inc(v_fvars_2403_);
v___x_2415_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2403_, v_f_2404_, v___x_2414_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
if (lean_obj_tag(v___x_2415_) == 0)
{
uint8_t v_implicits_2416_; 
v_implicits_2416_ = lean_ctor_get_uint8(v_a_2406_, 2);
if (v_implicits_2416_ == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; 
v_a_2417_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2415_, 1);
lean_inc(v_a_2412_);
lean_inc_ref(v_a_2411_);
lean_inc(v_a_2410_);
lean_inc_ref(v_a_2409_);
v___x_2418_ = lean_infer_type(v_f_2404_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
v___x_2420_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2419_, v_args_2405_, v___x_2414_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v_fst_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v_fst_2422_ = lean_ctor_get(v_a_2421_, 0);
lean_inc(v_fst_2422_);
lean_dec(v_a_2421_);
v___x_2423_ = lean_array_get_size(v_args_2405_);
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2423_, v_fst_2422_, v_fvars_2403_, v___x_2424_, v_args_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
lean_dec(v_fst_2422_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2434_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = l_Lean_mkAppN(v_a_2417_, v_a_2426_);
lean_dec(v_a_2426_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2430_);
v___x_2432_ = v___x_2428_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2417_);
v_a_2435_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2425_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2425_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v_a_2417_);
lean_dec_ref(v_args_2405_);
lean_dec(v_fvars_2403_);
v_a_2443_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2420_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2420_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
else
{
lean_dec(v_a_2417_);
lean_dec_ref(v_args_2405_);
lean_dec(v_fvars_2403_);
return v___x_2418_;
}
}
else
{
lean_object* v_a_2451_; size_t v_sz_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
lean_dec_ref(v_f_2404_);
v_a_2451_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2415_, 1);
v_sz_2452_ = lean_array_size(v_args_2405_);
v___x_2453_ = ((size_t)0ULL);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2403_, v_sz_2452_, v___x_2453_, v_args_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2463_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2463_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2463_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2459_ = l_Lean_mkAppN(v_a_2451_, v_a_2455_);
lean_dec(v_a_2455_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2459_);
v___x_2461_ = v___x_2457_;
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
lean_dec(v_a_2451_);
v_a_2464_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2454_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2454_);
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
lean_dec_ref(v_args_2405_);
lean_dec_ref(v_f_2404_);
lean_dec(v_fvars_2403_);
return v___x_2415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2472_, lean_object* v_f_2473_, lean_object* v_args_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2472_, v_f_2473_, v_args_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2484_, lean_object* v_b_2485_, uint8_t v___x_2486_, lean_object* v_mk_2487_, lean_object* v_a_2488_, lean_object* v_x_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_inc_ref(v_x_2489_);
v___x_2498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_x_2489_);
lean_ctor_set(v___x_2498_, 1, v_fvars_2484_);
v___x_2499_ = lean_expr_instantiate1(v_b_2485_, v_x_2489_);
v___x_2500_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2498_, v___x_2499_, v___x_2486_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2500_) == 0)
{
uint8_t v_lift_2501_; 
v_lift_2501_ = lean_ctor_get_uint8(v___y_2490_, 10);
if (v_lift_2501_ == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2514_; 
v_a_2502_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2504_ = v___x_2500_;
v_isShared_2505_ = v_isSharedCheck_2514_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2500_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2514_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2506_ = lean_unsigned_to_nat(1u);
v___x_2507_ = lean_mk_empty_array_with_capacity(v___x_2506_);
v___x_2508_ = lean_array_push(v___x_2507_, v_x_2489_);
v___x_2509_ = lean_expr_abstract(v_a_2502_, v___x_2508_);
lean_dec_ref(v___x_2508_);
lean_dec(v_a_2502_);
v___x_2510_ = lean_apply_2(v_mk_2487_, v_a_2488_, v___x_2509_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2510_);
v___x_2512_ = v___x_2504_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_a_2515_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2516_ = l_Lean_Expr_fvarId_x21(v_x_2489_);
v___x_2517_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2516_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2531_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2531_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2531_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2522_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2518_, v_a_2515_);
lean_dec(v_a_2518_);
v___x_2523_ = lean_unsigned_to_nat(1u);
v___x_2524_ = lean_mk_empty_array_with_capacity(v___x_2523_);
v___x_2525_ = lean_array_push(v___x_2524_, v_x_2489_);
v___x_2526_ = lean_expr_abstract(v___x_2522_, v___x_2525_);
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2522_);
v___x_2527_ = lean_apply_2(v_mk_2487_, v_a_2488_, v___x_2526_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2527_);
v___x_2529_ = v___x_2520_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_a_2515_);
lean_dec_ref(v_x_2489_);
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_mk_2487_);
v_a_2532_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2517_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2517_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2489_);
lean_dec_ref(v_a_2488_);
lean_dec_ref(v_mk_2487_);
return v___x_2500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2540_, lean_object* v_b_2541_, lean_object* v___x_2542_, lean_object* v_mk_2543_, lean_object* v_a_2544_, lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
uint8_t v___x_50336__boxed_2554_; lean_object* v_res_2555_; 
v___x_50336__boxed_2554_ = lean_unbox(v___x_2542_);
v_res_2555_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2540_, v_b_2541_, v___x_50336__boxed_2554_, v_mk_2543_, v_a_2544_, v_x_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v_b_2541_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2556_, lean_object* v_n_2557_, lean_object* v_t_2558_, lean_object* v_b_2559_, uint8_t v_i_2560_, lean_object* v_mk_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
uint8_t v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = 0;
lean_inc(v_fvars_2556_);
v___x_2571_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2556_, v_t_2558_, v___x_2570_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2571_) == 0)
{
uint8_t v_underBinder_2572_; 
v_underBinder_2572_ = lean_ctor_get_uint8(v_a_2562_, 4);
if (v_underBinder_2572_ == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_n_2557_);
lean_dec(v_fvars_2556_);
v_a_2573_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2575_ = v___x_2571_;
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2571_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_apply_2(v_mk_2561_, v_a_2573_, v_b_2559_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2577_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; 
v_a_2582_ = lean_ctor_get(v___x_2571_, 0);
lean_inc_n(v_a_2582_, 2);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2583_ = lean_box(v___x_2570_);
v___f_2584_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2584_, 0, v_fvars_2556_);
lean_closure_set(v___f_2584_, 1, v_b_2559_);
lean_closure_set(v___f_2584_, 2, v___x_2583_);
lean_closure_set(v___f_2584_, 3, v_mk_2561_);
lean_closure_set(v___f_2584_, 4, v_a_2582_);
v___x_2585_ = 0;
v___x_2586_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2557_, v_i_2560_, v_a_2582_, v___f_2584_, v___x_2585_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
return v___x_2586_;
}
}
else
{
lean_dec_ref(v_mk_2561_);
lean_dec_ref(v_b_2559_);
lean_dec(v_n_2557_);
lean_dec(v_fvars_2556_);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2587_, lean_object* v_n_2588_, lean_object* v_t_2589_, lean_object* v_b_2590_, lean_object* v_i_2591_, lean_object* v_mk_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
uint8_t v_i_boxed_2601_; lean_object* v_res_2602_; 
v_i_boxed_2601_ = lean_unbox(v_i_2591_);
v_res_2602_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2587_, v_n_2588_, v_t_2589_, v_b_2590_, v_i_boxed_2601_, v_mk_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2603_, lean_object* v_e_2604_, lean_object* v_topLevel_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
uint8_t v_topLevel_boxed_2614_; lean_object* v_res_2615_; 
v_topLevel_boxed_2614_ = lean_unbox(v_topLevel_2605_);
v_res_2615_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2603_, v_e_2604_, v_topLevel_boxed_2614_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
return v_res_2615_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2620_ = lean_unsigned_to_nat(27u);
v___x_2621_ = lean_unsigned_to_nat(1964u);
v___x_2622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2624_ = l_mkPanicMessageWithDecl(v___x_2623_, v___x_2622_, v___x_2621_, v___x_2620_, v___x_2619_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2625_, lean_object* v_fvars_2626_, lean_object* v_b_2627_, uint8_t v___x_2628_, lean_object* v_e_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, uint8_t v_isLet_2632_, uint8_t v_topLevel_2633_, lean_object* v_x_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
if (v_fst_2625_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_inc_ref(v_x_2634_);
v___x_2643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2643_, 0, v_x_2634_);
lean_ctor_set(v___x_2643_, 1, v_fvars_2626_);
v___x_2644_ = lean_expr_instantiate1(v_b_2627_, v_x_2634_);
v___x_2645_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2643_, v___x_2644_, v___x_2628_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2645_) == 0)
{
if (lean_obj_tag(v_e_2629_) == 8)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2681_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2681_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2681_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_declName_2650_; lean_object* v_type_2651_; lean_object* v_value_2652_; lean_object* v_body_2653_; uint8_t v_nondep_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___y_2660_; size_t v___x_2675_; size_t v___x_2676_; uint8_t v___x_2677_; 
v_declName_2650_ = lean_ctor_get(v_e_2629_, 0);
v_type_2651_ = lean_ctor_get(v_e_2629_, 1);
v_value_2652_ = lean_ctor_get(v_e_2629_, 2);
v_body_2653_ = lean_ctor_get(v_e_2629_, 3);
v_nondep_2654_ = lean_ctor_get_uint8(v_e_2629_, sizeof(void*)*4 + 8);
v___x_2655_ = lean_unsigned_to_nat(1u);
v___x_2656_ = lean_mk_empty_array_with_capacity(v___x_2655_);
v___x_2657_ = lean_array_push(v___x_2656_, v_x_2634_);
v___x_2658_ = lean_expr_abstract(v_a_2646_, v___x_2657_);
lean_dec_ref(v___x_2657_);
lean_dec(v_a_2646_);
v___x_2675_ = lean_ptr_addr(v_type_2651_);
v___x_2676_ = lean_ptr_addr(v_a_2630_);
v___x_2677_ = lean_usize_dec_eq(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
v___y_2660_ = v___x_2677_;
goto v___jp_2659_;
}
else
{
size_t v___x_2678_; size_t v___x_2679_; uint8_t v___x_2680_; 
v___x_2678_ = lean_ptr_addr(v_value_2652_);
v___x_2679_ = lean_ptr_addr(v_a_2631_);
v___x_2680_ = lean_usize_dec_eq(v___x_2678_, v___x_2679_);
v___y_2660_ = v___x_2680_;
goto v___jp_2659_;
}
v___jp_2659_:
{
if (v___y_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
lean_inc(v_declName_2650_);
lean_dec_ref_known(v_e_2629_, 4);
v___x_2661_ = l_Lean_Expr_letE___override(v_declName_2650_, v_a_2630_, v_a_2631_, v___x_2658_, v_nondep_2654_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2661_);
v___x_2663_ = v___x_2648_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
else
{
size_t v___x_2665_; size_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_ptr_addr(v_body_2653_);
v___x_2666_ = lean_ptr_addr(v___x_2658_);
v___x_2667_ = lean_usize_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_inc(v_declName_2650_);
lean_dec_ref_known(v_e_2629_, 4);
v___x_2668_ = l_Lean_Expr_letE___override(v_declName_2650_, v_a_2630_, v_a_2631_, v___x_2658_, v_nondep_2654_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2668_);
v___x_2670_ = v___x_2648_;
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
lean_object* v___x_2673_; 
lean_dec_ref(v___x_2658_);
lean_dec_ref(v_a_2631_);
lean_dec_ref(v_a_2630_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_e_2629_);
v___x_2673_ = v___x_2648_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_e_2629_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
else
{
lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_x_2634_);
lean_dec_ref(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec_ref(v_e_2629_);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v___x_2645_, 0);
lean_dec(v_unused_2691_);
v___x_2683_ = v___x_2645_;
v_isShared_2684_ = v_isSharedCheck_2690_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v___x_2645_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2690_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2686_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2685_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2686_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_dec_ref(v_x_2634_);
lean_dec_ref(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec_ref(v_e_2629_);
return v___x_2645_;
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec_ref(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec_ref(v_e_2629_);
v___x_2692_ = l_Lean_Expr_fvarId_x21(v_x_2634_);
v___x_2693_ = l_Lean_FVarId_getDecl___redArg(v___x_2692_, v___y_2638_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2695_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2694_, v_isLet_2632_, v___y_2635_, v___y_2637_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_dec_ref_known(v___x_2695_, 1);
v___x_2696_ = lean_expr_instantiate1(v_b_2627_, v_x_2634_);
lean_dec_ref(v_x_2634_);
v___x_2697_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2626_, v___x_2696_, v_topLevel_2633_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2697_;
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v_x_2634_);
lean_dec(v_fvars_2626_);
v_a_2698_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2695_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2695_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_x_2634_);
lean_dec(v_fvars_2626_);
v_a_2706_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2693_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2693_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2714_ = _args[0];
lean_object* v_fvars_2715_ = _args[1];
lean_object* v_b_2716_ = _args[2];
lean_object* v___x_2717_ = _args[3];
lean_object* v_e_2718_ = _args[4];
lean_object* v_a_2719_ = _args[5];
lean_object* v_a_2720_ = _args[6];
lean_object* v_isLet_2721_ = _args[7];
lean_object* v_topLevel_2722_ = _args[8];
lean_object* v_x_2723_ = _args[9];
lean_object* v___y_2724_ = _args[10];
lean_object* v___y_2725_ = _args[11];
lean_object* v___y_2726_ = _args[12];
lean_object* v___y_2727_ = _args[13];
lean_object* v___y_2728_ = _args[14];
lean_object* v___y_2729_ = _args[15];
lean_object* v___y_2730_ = _args[16];
lean_object* v___y_2731_ = _args[17];
_start:
{
uint8_t v_fst_50476__boxed_2732_; uint8_t v___x_50477__boxed_2733_; uint8_t v_isLet_boxed_2734_; uint8_t v_topLevel_boxed_2735_; lean_object* v_res_2736_; 
v_fst_50476__boxed_2732_ = lean_unbox(v_fst_2714_);
v___x_50477__boxed_2733_ = lean_unbox(v___x_2717_);
v_isLet_boxed_2734_ = lean_unbox(v_isLet_2721_);
v_topLevel_boxed_2735_ = lean_unbox(v_topLevel_2722_);
v_res_2736_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_50476__boxed_2732_, v_fvars_2715_, v_b_2716_, v___x_50477__boxed_2733_, v_e_2718_, v_a_2719_, v_a_2720_, v_isLet_boxed_2734_, v_topLevel_boxed_2735_, v_x_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec_ref(v_b_2716_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2737_, lean_object* v_e_2738_, uint8_t v_isLet_2739_, lean_object* v_n_2740_, lean_object* v_t_2741_, lean_object* v_v_2742_, lean_object* v_b_2743_, uint8_t v_topLevel_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = 0;
lean_inc(v_fvars_2737_);
v___x_2768_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2737_, v_t_2741_, v___x_2767_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2879_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2879_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2879_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; 
lean_inc(v_fvars_2737_);
v___x_2773_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2737_, v_v_2742_, v___x_2767_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2878_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2878_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2878_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2791_; lean_object* v___y_2792_; uint8_t v___y_2793_; uint8_t v___y_2794_; uint8_t v_descend_2826_; uint8_t v_underBinder_2827_; uint8_t v_usedOnly_2828_; uint8_t v_merge_2829_; uint8_t v_lift_2830_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; 
v_descend_2826_ = lean_ctor_get_uint8(v_a_2745_, 3);
v_underBinder_2827_ = lean_ctor_get_uint8(v_a_2745_, 4);
v_usedOnly_2828_ = lean_ctor_get_uint8(v_a_2745_, 5);
v_merge_2829_ = lean_ctor_get_uint8(v_a_2745_, 6);
v_lift_2830_ = lean_ctor_get_uint8(v_a_2745_, 10);
if (v_usedOnly_2828_ == 0)
{
goto v___jp_2859_;
}
else
{
uint8_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = l_Lean_Expr_hasLooseBVars(v_b_2743_);
v___x_2876_ = lean_bool_not(v___x_2875_);
if (v___x_2876_ == 0)
{
goto v___jp_2859_;
}
else
{
lean_object* v___x_2877_; 
lean_del_object(v___x_2776_);
lean_dec(v_a_2774_);
lean_del_object(v___x_2771_);
lean_dec(v_a_2769_);
lean_dec(v_n_2740_);
lean_dec_ref(v_e_2738_);
v___x_2877_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2737_, v_b_2743_, v_topLevel_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2877_;
}
}
v___jp_2778_:
{
uint8_t v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = 0;
v___x_2789_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2786_, v_a_2769_, v_a_2774_, v___y_2779_, v___x_2767_, v___x_2788_, v___y_2785_, v___y_2784_, v___y_2787_, v___y_2783_, v___y_2782_, v___y_2781_, v___y_2780_);
return v___x_2789_;
}
v___jp_2790_:
{
if (v___y_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_e_2738_);
v___x_2795_ = l_Lean_Expr_letE___override(v___y_2791_, v_a_2769_, v_a_2774_, v_b_2743_, v___y_2793_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2795_);
v___x_2797_ = v___x_2776_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
else
{
size_t v___x_2799_; size_t v___x_2800_; uint8_t v___x_2801_; 
v___x_2799_ = lean_ptr_addr(v___y_2792_);
lean_dec_ref(v___y_2792_);
v___x_2800_ = lean_ptr_addr(v_b_2743_);
v___x_2801_ = lean_usize_dec_eq(v___x_2799_, v___x_2800_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
lean_dec_ref(v_e_2738_);
v___x_2802_ = l_Lean_Expr_letE___override(v___y_2791_, v_a_2769_, v_a_2774_, v_b_2743_, v___y_2793_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2802_);
v___x_2804_ = v___x_2776_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
else
{
lean_object* v___x_2807_; 
lean_dec(v___y_2791_);
lean_dec(v_a_2774_);
lean_dec(v_a_2769_);
lean_dec_ref(v_b_2743_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v_e_2738_);
v___x_2807_ = v___x_2776_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_e_2738_);
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
v___jp_2809_:
{
if (lean_obj_tag(v_e_2738_) == 8)
{
lean_object* v_declName_2810_; lean_object* v_type_2811_; lean_object* v_value_2812_; lean_object* v_body_2813_; uint8_t v_nondep_2814_; size_t v___x_2815_; size_t v___x_2816_; uint8_t v___x_2817_; 
lean_del_object(v___x_2771_);
v_declName_2810_ = lean_ctor_get(v_e_2738_, 0);
v_type_2811_ = lean_ctor_get(v_e_2738_, 1);
v_value_2812_ = lean_ctor_get(v_e_2738_, 2);
v_body_2813_ = lean_ctor_get(v_e_2738_, 3);
v_nondep_2814_ = lean_ctor_get_uint8(v_e_2738_, sizeof(void*)*4 + 8);
v___x_2815_ = lean_ptr_addr(v_type_2811_);
v___x_2816_ = lean_ptr_addr(v_a_2769_);
v___x_2817_ = lean_usize_dec_eq(v___x_2815_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_inc_ref(v_body_2813_);
lean_inc(v_declName_2810_);
v___y_2791_ = v_declName_2810_;
v___y_2792_ = v_body_2813_;
v___y_2793_ = v_nondep_2814_;
v___y_2794_ = v___x_2817_;
goto v___jp_2790_;
}
else
{
size_t v___x_2818_; size_t v___x_2819_; uint8_t v___x_2820_; 
v___x_2818_ = lean_ptr_addr(v_value_2812_);
v___x_2819_ = lean_ptr_addr(v_a_2774_);
v___x_2820_ = lean_usize_dec_eq(v___x_2818_, v___x_2819_);
lean_inc_ref(v_body_2813_);
lean_inc(v_declName_2810_);
v___y_2791_ = v_declName_2810_;
v___y_2792_ = v_body_2813_;
v___y_2793_ = v_nondep_2814_;
v___y_2794_ = v___x_2820_;
goto v___jp_2790_;
}
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
lean_del_object(v___x_2776_);
lean_dec(v_a_2774_);
lean_dec(v_a_2769_);
lean_dec_ref(v_b_2743_);
lean_dec_ref(v_e_2738_);
v___x_2821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2822_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2821_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2822_);
v___x_2824_ = v___x_2771_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
v___jp_2831_:
{
lean_object* v___x_2839_; 
lean_inc(v_a_2774_);
lean_inc(v_a_2769_);
v___x_2839_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2737_, v_n_2740_, v_a_2769_, v_a_2774_, v___y_2832_, v___y_2834_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v_fst_2841_; lean_object* v_snd_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___f_2846_; uint8_t v___x_2847_; uint8_t v___x_2848_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v_fst_2841_ = lean_ctor_get(v_a_2840_, 0);
lean_inc_n(v_fst_2841_, 2);
v_snd_2842_ = lean_ctor_get(v_a_2840_, 1);
lean_inc(v_snd_2842_);
lean_dec(v_a_2840_);
v___x_2843_ = lean_box(v___x_2767_);
v___x_2844_ = lean_box(v_isLet_2739_);
v___x_2845_ = lean_box(v_topLevel_2744_);
lean_inc(v_a_2774_);
lean_inc(v_a_2769_);
lean_inc_ref(v_e_2738_);
lean_inc_ref(v_b_2743_);
v___f_2846_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2846_, 0, v_fst_2841_);
lean_closure_set(v___f_2846_, 1, v_fvars_2737_);
lean_closure_set(v___f_2846_, 2, v_b_2743_);
lean_closure_set(v___f_2846_, 3, v___x_2843_);
lean_closure_set(v___f_2846_, 4, v_e_2738_);
lean_closure_set(v___f_2846_, 5, v_a_2769_);
lean_closure_set(v___f_2846_, 6, v_a_2774_);
lean_closure_set(v___f_2846_, 7, v___x_2844_);
lean_closure_set(v___f_2846_, 8, v___x_2845_);
v___x_2847_ = lean_unbox(v_fst_2841_);
lean_dec(v_fst_2841_);
v___x_2848_ = lean_bool_not(v___x_2847_);
if (v___x_2848_ == 0)
{
lean_del_object(v___x_2776_);
lean_del_object(v___x_2771_);
lean_dec_ref(v_b_2743_);
lean_dec_ref(v_e_2738_);
v___y_2779_ = v___f_2846_;
v___y_2780_ = v___y_2838_;
v___y_2781_ = v___y_2837_;
v___y_2782_ = v___y_2836_;
v___y_2783_ = v___y_2835_;
v___y_2784_ = v___y_2833_;
v___y_2785_ = v___y_2832_;
v___y_2786_ = v_snd_2842_;
v___y_2787_ = v___y_2834_;
goto v___jp_2778_;
}
else
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_bool_not(v_underBinder_2827_);
if (v___x_2849_ == 0)
{
uint8_t v___x_2850_; 
v___x_2850_ = lean_bool_not(v_descend_2826_);
if (v___x_2850_ == 0)
{
lean_del_object(v___x_2776_);
lean_del_object(v___x_2771_);
lean_dec_ref(v_b_2743_);
lean_dec_ref(v_e_2738_);
v___y_2779_ = v___f_2846_;
v___y_2780_ = v___y_2838_;
v___y_2781_ = v___y_2837_;
v___y_2782_ = v___y_2836_;
v___y_2783_ = v___y_2835_;
v___y_2784_ = v___y_2833_;
v___y_2785_ = v___y_2832_;
v___y_2786_ = v_snd_2842_;
v___y_2787_ = v___y_2834_;
goto v___jp_2778_;
}
else
{
lean_dec_ref(v___f_2846_);
lean_dec(v_snd_2842_);
goto v___jp_2809_;
}
}
else
{
lean_dec_ref(v___f_2846_);
lean_dec(v_snd_2842_);
goto v___jp_2809_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_del_object(v___x_2776_);
lean_dec(v_a_2774_);
lean_del_object(v___x_2771_);
lean_dec(v_a_2769_);
lean_dec_ref(v_b_2743_);
lean_dec_ref(v_e_2738_);
lean_dec(v_fvars_2737_);
v_a_2851_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2839_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2839_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
v___jp_2859_:
{
if (v_merge_2829_ == 0)
{
v___y_2832_ = v_a_2745_;
v___y_2833_ = v_a_2746_;
v___y_2834_ = v_a_2747_;
v___y_2835_ = v_a_2748_;
v___y_2836_ = v_a_2749_;
v___y_2837_ = v_a_2750_;
v___y_2838_ = v_a_2751_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2860_; lean_object* v_valueMap_2861_; lean_object* v___x_2862_; 
v___x_2860_ = lean_st_ref_get(v_a_2747_);
v_valueMap_2861_ = lean_ctor_get(v___x_2860_, 2);
lean_inc_ref(v_valueMap_2861_);
lean_dec(v___x_2860_);
v___x_2862_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2861_, v_a_2774_);
lean_dec_ref(v_valueMap_2861_);
if (lean_obj_tag(v___x_2862_) == 1)
{
lean_del_object(v___x_2776_);
lean_dec(v_a_2774_);
lean_del_object(v___x_2771_);
lean_dec(v_a_2769_);
lean_dec(v_n_2740_);
lean_dec_ref(v_e_2738_);
if (v_isLet_2739_ == 0)
{
lean_object* v_val_2863_; 
v_val_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v___y_2754_ = v_val_2863_;
v___y_2755_ = v_a_2745_;
v___y_2756_ = v_a_2746_;
v___y_2757_ = v_a_2747_;
v___y_2758_ = v_a_2748_;
v___y_2759_ = v_a_2749_;
v___y_2760_ = v_a_2750_;
v___y_2761_ = v_a_2751_;
goto v___jp_2753_;
}
else
{
if (v_lift_2830_ == 0)
{
lean_object* v_val_2864_; 
v_val_2864_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_val_2864_);
lean_dec_ref_known(v___x_2862_, 1);
v___y_2754_ = v_val_2864_;
v___y_2755_ = v_a_2745_;
v___y_2756_ = v_a_2746_;
v___y_2757_ = v_a_2747_;
v___y_2758_ = v_a_2748_;
v___y_2759_ = v_a_2749_;
v___y_2760_ = v_a_2750_;
v___y_2761_ = v_a_2751_;
goto v___jp_2753_;
}
else
{
lean_object* v_val_2865_; lean_object* v___x_2866_; 
v_val_2865_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_val_2865_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2866_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2865_, v_a_2747_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_dec_ref_known(v___x_2866_, 1);
v___y_2754_ = v_val_2865_;
v___y_2755_ = v_a_2745_;
v___y_2756_ = v_a_2746_;
v___y_2757_ = v_a_2747_;
v___y_2758_ = v_a_2748_;
v___y_2759_ = v_a_2749_;
v___y_2760_ = v_a_2750_;
v___y_2761_ = v_a_2751_;
goto v___jp_2753_;
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_val_2865_);
lean_dec_ref(v_b_2743_);
lean_dec(v_fvars_2737_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2862_);
v___y_2832_ = v_a_2745_;
v___y_2833_ = v_a_2746_;
v___y_2834_ = v_a_2747_;
v___y_2835_ = v_a_2748_;
v___y_2836_ = v_a_2749_;
v___y_2837_ = v_a_2750_;
v___y_2838_ = v_a_2751_;
goto v___jp_2831_;
}
}
}
}
}
else
{
lean_del_object(v___x_2771_);
lean_dec(v_a_2769_);
lean_dec_ref(v_b_2743_);
lean_dec(v_n_2740_);
lean_dec_ref(v_e_2738_);
lean_dec(v_fvars_2737_);
return v___x_2773_;
}
}
}
else
{
lean_dec_ref(v_b_2743_);
lean_dec_ref(v_v_2742_);
lean_dec(v_n_2740_);
lean_dec_ref(v_e_2738_);
lean_dec(v_fvars_2737_);
return v___x_2768_;
}
v___jp_2753_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_inc(v___y_2754_);
v___x_2762_ = l_Lean_Expr_fvar___override(v___y_2754_);
v___x_2763_ = lean_expr_instantiate1(v_b_2743_, v___x_2762_);
lean_dec_ref(v___x_2762_);
lean_dec_ref(v_b_2743_);
v___x_2764_ = lean_box(v_topLevel_2744_);
v___x_2765_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2765_, 0, v_fvars_2737_);
lean_closure_set(v___x_2765_, 1, v___x_2763_);
lean_closure_set(v___x_2765_, 2, v___x_2764_);
v___x_2766_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2754_, v___x_2765_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2754_);
return v___x_2766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2880_, lean_object* v_struct_2881_, lean_object* v___x_2882_, lean_object* v_typeName_2883_, lean_object* v_idx_2884_, lean_object* v_e_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
uint8_t v___x_50257__boxed_2894_; lean_object* v_res_2895_; 
v___x_50257__boxed_2894_ = lean_unbox(v___x_2882_);
v_res_2895_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2880_, v_struct_2881_, v___x_50257__boxed_2894_, v_typeName_2883_, v_idx_2884_, v_e_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2895_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2899_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2900_ = lean_unsigned_to_nat(75u);
v___x_2901_ = lean_unsigned_to_nat(229u);
v___x_2902_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2903_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2904_ = l_mkPanicMessageWithDecl(v___x_2903_, v___x_2902_, v___x_2901_, v___x_2900_, v___x_2899_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2905_, lean_object* v_e_2906_, lean_object* v_fvars_2907_, uint8_t v_topLevel_2908_, uint8_t v___x_2909_, lean_object* v_____r_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_k_2920_; 
switch(lean_obj_tag(v_e_2906_))
{
case 5:
{
lean_object* v___x_2923_; lean_object* v_dummy_2924_; lean_object* v_nargs_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2923_ = l_Lean_Expr_getAppFn(v_e_2906_);
v_dummy_2924_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2925_ = l_Lean_Expr_getAppNumArgs(v_e_2906_);
lean_inc(v_nargs_2925_);
v___x_2926_ = lean_mk_array(v_nargs_2925_, v_dummy_2924_);
v___x_2927_ = lean_unsigned_to_nat(1u);
v___x_2928_ = lean_nat_sub(v_nargs_2925_, v___x_2927_);
lean_dec(v_nargs_2925_);
lean_inc_ref(v_e_2906_);
v___x_2929_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2906_, v___x_2926_, v___x_2928_);
v___x_2930_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2930_, 0, v_fvars_2907_);
lean_closure_set(v___x_2930_, 1, v___x_2923_);
lean_closure_set(v___x_2930_, 2, v___x_2929_);
v_k_2920_ = v___x_2930_;
goto v___jp_2919_;
}
case 6:
{
lean_object* v_binderName_2931_; lean_object* v_binderType_2932_; lean_object* v_body_2933_; uint8_t v_binderInfo_2934_; lean_object* v___x_2935_; lean_object* v___f_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_binderName_2931_ = lean_ctor_get(v_e_2906_, 0);
v_binderType_2932_ = lean_ctor_get(v_e_2906_, 1);
v_body_2933_ = lean_ctor_get(v_e_2906_, 2);
v_binderInfo_2934_ = lean_ctor_get_uint8(v_e_2906_, sizeof(void*)*3 + 8);
v___x_2935_ = lean_box(v_binderInfo_2934_);
lean_inc_ref_n(v_body_2933_, 2);
lean_inc_ref_n(v_binderType_2932_, 2);
lean_inc_ref(v_e_2906_);
lean_inc_n(v_binderName_2931_, 2);
v___f_2936_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2936_, 0, v_binderName_2931_);
lean_closure_set(v___f_2936_, 1, v___x_2935_);
lean_closure_set(v___f_2936_, 2, v_e_2906_);
lean_closure_set(v___f_2936_, 3, v_binderType_2932_);
lean_closure_set(v___f_2936_, 4, v_body_2933_);
v___x_2937_ = lean_box(v_binderInfo_2934_);
v___x_2938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2938_, 0, v_fvars_2907_);
lean_closure_set(v___x_2938_, 1, v_binderName_2931_);
lean_closure_set(v___x_2938_, 2, v_binderType_2932_);
lean_closure_set(v___x_2938_, 3, v_body_2933_);
lean_closure_set(v___x_2938_, 4, v___x_2937_);
lean_closure_set(v___x_2938_, 5, v___f_2936_);
v_k_2920_ = v___x_2938_;
goto v___jp_2919_;
}
case 7:
{
lean_object* v_binderName_2939_; lean_object* v_binderType_2940_; lean_object* v_body_2941_; uint8_t v_binderInfo_2942_; lean_object* v___x_2943_; lean_object* v___f_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_binderName_2939_ = lean_ctor_get(v_e_2906_, 0);
v_binderType_2940_ = lean_ctor_get(v_e_2906_, 1);
v_body_2941_ = lean_ctor_get(v_e_2906_, 2);
v_binderInfo_2942_ = lean_ctor_get_uint8(v_e_2906_, sizeof(void*)*3 + 8);
v___x_2943_ = lean_box(v_binderInfo_2942_);
lean_inc_ref_n(v_body_2941_, 2);
lean_inc_ref_n(v_binderType_2940_, 2);
lean_inc_ref(v_e_2906_);
lean_inc_n(v_binderName_2939_, 2);
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2944_, 0, v_binderName_2939_);
lean_closure_set(v___f_2944_, 1, v___x_2943_);
lean_closure_set(v___f_2944_, 2, v_e_2906_);
lean_closure_set(v___f_2944_, 3, v_binderType_2940_);
lean_closure_set(v___f_2944_, 4, v_body_2941_);
v___x_2945_ = lean_box(v_binderInfo_2942_);
v___x_2946_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2946_, 0, v_fvars_2907_);
lean_closure_set(v___x_2946_, 1, v_binderName_2939_);
lean_closure_set(v___x_2946_, 2, v_binderType_2940_);
lean_closure_set(v___x_2946_, 3, v_body_2941_);
lean_closure_set(v___x_2946_, 4, v___x_2945_);
lean_closure_set(v___x_2946_, 5, v___f_2944_);
v_k_2920_ = v___x_2946_;
goto v___jp_2919_;
}
case 8:
{
lean_object* v_declName_2947_; lean_object* v_type_2948_; lean_object* v_value_2949_; lean_object* v_body_2950_; uint8_t v_nondep_2951_; uint8_t v___x_2952_; lean_object* v___x_2953_; 
v_declName_2947_ = lean_ctor_get(v_e_2906_, 0);
lean_inc(v_declName_2947_);
v_type_2948_ = lean_ctor_get(v_e_2906_, 1);
lean_inc_ref(v_type_2948_);
v_value_2949_ = lean_ctor_get(v_e_2906_, 2);
lean_inc_ref(v_value_2949_);
v_body_2950_ = lean_ctor_get(v_e_2906_, 3);
lean_inc_ref(v_body_2950_);
v_nondep_2951_ = lean_ctor_get_uint8(v_e_2906_, sizeof(void*)*4 + 8);
v___x_2952_ = lean_bool_not(v_nondep_2951_);
v___x_2953_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2907_, v_e_2906_, v___x_2952_, v_declName_2947_, v_type_2948_, v_value_2949_, v_body_2950_, v_topLevel_2908_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2953_;
}
case 10:
{
lean_object* v_data_2954_; lean_object* v_expr_2955_; lean_object* v___x_2956_; 
v_data_2954_ = lean_ctor_get(v_e_2906_, 0);
v_expr_2955_ = lean_ctor_get(v_e_2906_, 1);
lean_inc_ref(v_expr_2955_);
v___x_2956_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2907_, v_expr_2955_, v_topLevel_2908_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2971_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2971_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2971_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
size_t v___x_2961_; size_t v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = lean_ptr_addr(v_expr_2955_);
v___x_2962_ = lean_ptr_addr(v_a_2957_);
v___x_2963_ = lean_usize_dec_eq(v___x_2961_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
lean_inc(v_data_2954_);
lean_dec_ref_known(v_e_2906_, 2);
v___x_2964_ = l_Lean_Expr_mdata___override(v_data_2954_, v_a_2957_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2964_);
v___x_2966_ = v___x_2959_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
else
{
lean_object* v___x_2969_; 
lean_dec(v_a_2957_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v_e_2906_);
v___x_2969_ = v___x_2959_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_e_2906_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2906_, 2);
return v___x_2956_;
}
}
case 11:
{
lean_object* v_typeName_2972_; lean_object* v_idx_2973_; lean_object* v_struct_2974_; lean_object* v___x_2975_; lean_object* v___f_2976_; 
v_typeName_2972_ = lean_ctor_get(v_e_2906_, 0);
v_idx_2973_ = lean_ctor_get(v_e_2906_, 1);
v_struct_2974_ = lean_ctor_get(v_e_2906_, 2);
v___x_2975_ = lean_box(v___x_2909_);
lean_inc_ref(v_e_2906_);
lean_inc(v_idx_2973_);
lean_inc(v_typeName_2972_);
lean_inc_ref(v_struct_2974_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2976_, 0, v_fvars_2907_);
lean_closure_set(v___f_2976_, 1, v_struct_2974_);
lean_closure_set(v___f_2976_, 2, v___x_2975_);
lean_closure_set(v___f_2976_, 3, v_typeName_2972_);
lean_closure_set(v___f_2976_, 4, v_idx_2973_);
lean_closure_set(v___f_2976_, 5, v_e_2906_);
v_k_2920_ = v___f_2976_;
goto v___jp_2919_;
}
default: 
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec(v_fvars_2907_);
lean_dec_ref(v_e_2906_);
v___x_2977_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2978_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2977_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2978_;
}
}
v___jp_2919_:
{
if (v_descend_2905_ == 0)
{
lean_object* v___x_2921_; 
lean_dec_ref(v_k_2920_);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_e_2906_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref(v_e_2906_);
lean_inc(v___y_2917_);
lean_inc_ref(v___y_2916_);
lean_inc(v___y_2915_);
lean_inc_ref(v___y_2914_);
lean_inc(v___y_2913_);
lean_inc(v___y_2912_);
lean_inc_ref(v___y_2911_);
v___x_2922_ = lean_apply_8(v_k_2920_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, lean_box(0));
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2979_, lean_object* v_e_2980_, lean_object* v_fvars_2981_, lean_object* v_topLevel_2982_, lean_object* v___x_2983_, lean_object* v_____r_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
uint8_t v_descend_boxed_2993_; uint8_t v_topLevel_boxed_2994_; uint8_t v___x_50410__boxed_2995_; lean_object* v_res_2996_; 
v_descend_boxed_2993_ = lean_unbox(v_descend_2979_);
v_topLevel_boxed_2994_ = lean_unbox(v_topLevel_2982_);
v___x_50410__boxed_2995_ = lean_unbox(v___x_2983_);
v_res_2996_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2993_, v_e_2980_, v_fvars_2981_, v_topLevel_boxed_2994_, v___x_50410__boxed_2995_, v_____r_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_2997_, lean_object* v_e_2998_, uint8_t v_topLevel_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v___y_3009_; lean_object* v_a_3010_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3020_; lean_object* v___y_3021_; uint8_t v___x_3024_; 
v___x_3024_ = l_Lean_Expr_isAtomic(v_e_2998_);
if (v___x_3024_ == 0)
{
uint8_t v_proofs_3025_; uint8_t v_types_3026_; uint8_t v_descend_3027_; lean_object* v___y_3029_; lean_object* v___y_3030_; uint8_t v___y_3048_; uint8_t v___x_3072_; 
v_proofs_3025_ = lean_ctor_get_uint8(v_a_3000_, 0);
v_types_3026_ = lean_ctor_get_uint8(v_a_3000_, 1);
v_descend_3027_ = lean_ctor_get_uint8(v_a_3000_, 3);
v___x_3072_ = lean_bool_not(v_descend_3027_);
if (v___x_3072_ == 0)
{
v___y_3048_ = v___x_3072_;
goto v___jp_3047_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_bool_not(v_topLevel_2999_);
v___y_3048_ = v___x_3073_;
goto v___jp_3047_;
}
v___jp_3028_:
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_bool_not(v_proofs_3025_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec_ref(v_e_2998_);
v___x_3032_ = lean_box(0);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc(v_a_3001_);
lean_inc_ref(v_a_3000_);
v___x_3033_ = lean_apply_9(v___y_3030_, v___x_3032_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, lean_box(0));
v___y_3016_ = v___y_3029_;
v___y_3017_ = v___x_3033_;
goto v___jp_3015_;
}
else
{
lean_object* v___x_3034_; 
lean_inc_ref(v_e_2998_);
v___x_3034_ = l_Lean_Meta_isProof(v_e_2998_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; uint8_t v___x_3036_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v___x_3036_ = lean_unbox(v_a_3035_);
lean_dec(v_a_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec_ref(v_e_2998_);
v___x_3037_ = lean_box(0);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc(v_a_3001_);
lean_inc_ref(v_a_3000_);
v___x_3038_ = lean_apply_9(v___y_3030_, v___x_3037_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, lean_box(0));
v___y_3016_ = v___y_3029_;
v___y_3017_ = v___x_3038_;
goto v___jp_3015_;
}
else
{
lean_dec_ref(v___y_3030_);
v___y_3009_ = v___y_3029_;
v_a_3010_ = v_e_2998_;
goto v___jp_3008_;
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_e_2998_);
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
}
v___jp_3047_:
{
if (v___y_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = lean_st_ref_get(v_a_3001_);
v___x_3050_ = lean_box(v_topLevel_2999_);
lean_inc_ref(v_e_2998_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v_e_2998_);
v___x_3052_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3049_, v___x_3051_);
lean_dec(v___x_3049_);
if (lean_obj_tag(v___x_3052_) == 0)
{
uint8_t v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = l_Lean_Meta_ExtractLets_containsLet(v_e_2998_);
v___x_3054_ = lean_bool_not(v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v___f_3060_; 
v___x_3055_ = lean_box(v_descend_3027_);
v___x_3056_ = lean_box(v_topLevel_2999_);
v___x_3057_ = lean_box(v___x_3054_);
lean_inc_ref_n(v_e_2998_, 2);
v___f_3058_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 14, 5);
lean_closure_set(v___f_3058_, 0, v___x_3055_);
lean_closure_set(v___f_3058_, 1, v_e_2998_);
lean_closure_set(v___f_3058_, 2, v_fvars_2997_);
lean_closure_set(v___f_3058_, 3, v___x_3056_);
lean_closure_set(v___f_3058_, 4, v___x_3057_);
v___x_3059_ = lean_box(v_types_3026_);
lean_inc_ref(v___f_3058_);
v___f_3060_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3060_, 0, v___x_3059_);
lean_closure_set(v___f_3060_, 1, v___f_3058_);
lean_closure_set(v___f_3060_, 2, v_e_2998_);
if (v_topLevel_2999_ == 0)
{
lean_dec_ref(v___f_3058_);
v___y_3029_ = v___x_3051_;
v___y_3030_ = v___f_3060_;
goto v___jp_3028_;
}
else
{
uint8_t v___x_3061_; 
v___x_3061_ = l_Lean_Expr_isLet(v_e_2998_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_Expr_isMData(v_e_2998_);
if (v___x_3062_ == 0)
{
lean_dec_ref(v___f_3058_);
v___y_3029_ = v___x_3051_;
v___y_3030_ = v___f_3060_;
goto v___jp_3028_;
}
else
{
lean_dec_ref(v___f_3060_);
lean_dec_ref(v_e_2998_);
v___y_3020_ = v___f_3058_;
v___y_3021_ = v___x_3051_;
goto v___jp_3019_;
}
}
else
{
lean_dec_ref(v___f_3060_);
lean_dec_ref(v_e_2998_);
v___y_3020_ = v___f_3058_;
v___y_3021_ = v___x_3051_;
goto v___jp_3019_;
}
}
}
else
{
lean_dec(v_fvars_2997_);
v___y_3009_ = v___x_3051_;
v_a_3010_ = v_e_2998_;
goto v___jp_3008_;
}
}
else
{
lean_object* v_val_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref_known(v___x_3051_, 2);
lean_dec_ref(v_e_2998_);
lean_dec(v_fvars_2997_);
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
else
{
lean_object* v___x_3071_; 
lean_dec(v_fvars_2997_);
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_e_2998_);
return v___x_3071_;
}
}
}
else
{
lean_object* v___x_3074_; 
lean_dec(v_fvars_2997_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_e_2998_);
return v___x_3074_;
}
v___jp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3011_ = lean_st_ref_take(v_a_3001_);
lean_inc_ref(v_a_3010_);
v___x_3012_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3011_, v___y_3009_, v_a_3010_);
v___x_3013_ = lean_st_ref_set(v_a_3001_, v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_a_3010_);
return v___x_3014_;
}
v___jp_3015_:
{
if (lean_obj_tag(v___y_3017_) == 0)
{
lean_object* v_a_3018_; 
v_a_3018_ = lean_ctor_get(v___y_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___y_3017_, 1);
v___y_3009_ = v___y_3016_;
v_a_3010_ = v_a_3018_;
goto v___jp_3008_;
}
else
{
lean_dec_ref(v___y_3016_);
return v___y_3017_;
}
}
v___jp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_box(0);
lean_inc(v_a_3006_);
lean_inc_ref(v_a_3005_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc(v_a_3001_);
lean_inc_ref(v_a_3000_);
v___x_3023_ = lean_apply_9(v___y_3020_, v___x_3022_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, lean_box(0));
v___y_3016_ = v___y_3021_;
v___y_3017_ = v___x_3023_;
goto v___jp_3015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3075_, lean_object* v_struct_3076_, uint8_t v___x_3077_, lean_object* v_typeName_3078_, lean_object* v_idx_3079_, lean_object* v_e_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3089_; 
lean_inc_ref(v_struct_3076_);
v___x_3089_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3075_, v_struct_3076_, v___x_3077_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
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
lean_dec_ref_known(v___x_3322_, 1);
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
v___x_3374_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_dec_ref_known(v___x_3374_, 1);
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
v___x_3477_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
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
lean_dec_ref_known(v___x_3481_, 1);
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
v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_3487_, v___x_3488_, v_decls_3486_);
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
v___x_3604_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3876_, size_t v_x_3877_, size_t v_x_3878_, lean_object* v_x_3879_, lean_object* v_x_3880_){
_start:
{
if (lean_obj_tag(v_x_3876_) == 0)
{
lean_object* v_es_3881_; size_t v___x_3882_; size_t v___x_3883_; lean_object* v_j_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; 
v_es_3881_ = lean_ctor_get(v_x_3876_, 0);
v___x_3882_ = ((size_t)31ULL);
v___x_3883_ = lean_usize_land(v_x_3877_, v___x_3882_);
v_j_3884_ = lean_usize_to_nat(v___x_3883_);
v___x_3885_ = lean_array_get_size(v_es_3881_);
v___x_3886_ = lean_nat_dec_lt(v_j_3884_, v___x_3885_);
if (v___x_3886_ == 0)
{
lean_dec(v_j_3884_);
lean_dec(v_x_3880_);
lean_dec(v_x_3879_);
return v_x_3876_;
}
else
{
lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3925_; 
lean_inc_ref(v_es_3881_);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_x_3876_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; 
v_unused_3926_ = lean_ctor_get(v_x_3876_, 0);
lean_dec(v_unused_3926_);
v___x_3888_ = v_x_3876_;
v_isShared_3889_ = v_isSharedCheck_3925_;
goto v_resetjp_3887_;
}
else
{
lean_dec(v_x_3876_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3925_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v_v_3890_; lean_object* v___x_3891_; lean_object* v_xs_x27_3892_; lean_object* v___y_3894_; 
v_v_3890_ = lean_array_fget(v_es_3881_, v_j_3884_);
v___x_3891_ = lean_box(0);
v_xs_x27_3892_ = lean_array_fset(v_es_3881_, v_j_3884_, v___x_3891_);
switch(lean_obj_tag(v_v_3890_))
{
case 0:
{
lean_object* v_key_3899_; lean_object* v_val_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3910_; 
v_key_3899_ = lean_ctor_get(v_v_3890_, 0);
v_val_3900_ = lean_ctor_get(v_v_3890_, 1);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_v_3890_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3902_ = v_v_3890_;
v_isShared_3903_ = v_isSharedCheck_3910_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_val_3900_);
lean_inc(v_key_3899_);
lean_dec(v_v_3890_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3910_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
uint8_t v___x_3904_; 
v___x_3904_ = l_Lean_instBEqMVarId_beq(v_x_3879_, v_key_3899_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
lean_del_object(v___x_3902_);
v___x_3905_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3899_, v_val_3900_, v_x_3879_, v_x_3880_);
v___x_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
v___y_3894_ = v___x_3906_;
goto v___jp_3893_;
}
else
{
lean_object* v___x_3908_; 
lean_dec(v_val_3900_);
lean_dec(v_key_3899_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 1, v_x_3880_);
lean_ctor_set(v___x_3902_, 0, v_x_3879_);
v___x_3908_ = v___x_3902_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_x_3879_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_x_3880_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
v___y_3894_ = v___x_3908_;
goto v___jp_3893_;
}
}
}
}
case 1:
{
lean_object* v_node_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3923_; 
v_node_3911_ = lean_ctor_get(v_v_3890_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_v_3890_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3913_ = v_v_3890_;
v_isShared_3914_ = v_isSharedCheck_3923_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_node_3911_);
lean_dec(v_v_3890_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3923_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
size_t v___x_3915_; size_t v___x_3916_; size_t v___x_3917_; size_t v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3915_ = ((size_t)5ULL);
v___x_3916_ = lean_usize_shift_right(v_x_3877_, v___x_3915_);
v___x_3917_ = ((size_t)1ULL);
v___x_3918_ = lean_usize_add(v_x_3878_, v___x_3917_);
v___x_3919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3911_, v___x_3916_, v___x_3918_, v_x_3879_, v_x_3880_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3919_);
v___x_3921_ = v___x_3913_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
v___y_3894_ = v___x_3921_;
goto v___jp_3893_;
}
}
}
default: 
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3924_, 0, v_x_3879_);
lean_ctor_set(v___x_3924_, 1, v_x_3880_);
v___y_3894_ = v___x_3924_;
goto v___jp_3893_;
}
}
v___jp_3893_:
{
lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3895_ = lean_array_fset(v_xs_x27_3892_, v_j_3884_, v___y_3894_);
lean_dec(v_j_3884_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3895_);
v___x_3897_ = v___x_3888_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
else
{
lean_object* v_ks_3927_; lean_object* v_vs_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3948_; 
v_ks_3927_ = lean_ctor_get(v_x_3876_, 0);
v_vs_3928_ = lean_ctor_get(v_x_3876_, 1);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_x_3876_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3930_ = v_x_3876_;
v_isShared_3931_ = v_isSharedCheck_3948_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_vs_3928_);
lean_inc(v_ks_3927_);
lean_dec(v_x_3876_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3948_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_ks_3927_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_vs_3928_);
v___x_3933_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v_newNode_3934_; uint8_t v___y_3936_; size_t v___x_3942_; uint8_t v___x_3943_; 
v_newNode_3934_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3933_, v_x_3879_, v_x_3880_);
v___x_3942_ = ((size_t)7ULL);
v___x_3943_ = lean_usize_dec_le(v___x_3942_, v_x_3878_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3934_);
v___x_3945_ = lean_unsigned_to_nat(4u);
v___x_3946_ = lean_nat_dec_lt(v___x_3944_, v___x_3945_);
lean_dec(v___x_3944_);
v___y_3936_ = v___x_3946_;
goto v___jp_3935_;
}
else
{
v___y_3936_ = v___x_3943_;
goto v___jp_3935_;
}
v___jp_3935_:
{
if (v___y_3936_ == 0)
{
lean_object* v_ks_3937_; lean_object* v_vs_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_ks_3937_ = lean_ctor_get(v_newNode_3934_, 0);
lean_inc_ref(v_ks_3937_);
v_vs_3938_ = lean_ctor_get(v_newNode_3934_, 1);
lean_inc_ref(v_vs_3938_);
lean_dec_ref(v_newNode_3934_);
v___x_3939_ = lean_unsigned_to_nat(0u);
v___x_3940_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3941_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3878_, v_ks_3937_, v_vs_3938_, v___x_3939_, v___x_3940_);
lean_dec_ref(v_vs_3938_);
lean_dec_ref(v_ks_3937_);
return v___x_3941_;
}
else
{
return v_newNode_3934_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3949_, lean_object* v_keys_3950_, lean_object* v_vals_3951_, lean_object* v_i_3952_, lean_object* v_entries_3953_){
_start:
{
lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3954_ = lean_array_get_size(v_keys_3950_);
v___x_3955_ = lean_nat_dec_lt(v_i_3952_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_dec(v_i_3952_);
return v_entries_3953_;
}
else
{
lean_object* v_k_3956_; lean_object* v_v_3957_; uint64_t v___x_3958_; size_t v_h_3959_; size_t v___x_3960_; lean_object* v___x_3961_; size_t v___x_3962_; size_t v___x_3963_; size_t v___x_3964_; size_t v_h_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v_k_3956_ = lean_array_fget_borrowed(v_keys_3950_, v_i_3952_);
v_v_3957_ = lean_array_fget_borrowed(v_vals_3951_, v_i_3952_);
v___x_3958_ = l_Lean_instHashableMVarId_hash(v_k_3956_);
v_h_3959_ = lean_uint64_to_usize(v___x_3958_);
v___x_3960_ = ((size_t)5ULL);
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_3962_ = ((size_t)1ULL);
v___x_3963_ = lean_usize_sub(v_depth_3949_, v___x_3962_);
v___x_3964_ = lean_usize_mul(v___x_3960_, v___x_3963_);
v_h_3965_ = lean_usize_shift_right(v_h_3959_, v___x_3964_);
v___x_3966_ = lean_nat_add(v_i_3952_, v___x_3961_);
lean_dec(v_i_3952_);
lean_inc(v_v_3957_);
lean_inc(v_k_3956_);
v___x_3967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3953_, v_h_3965_, v_depth_3949_, v_k_3956_, v_v_3957_);
v_i_3952_ = v___x_3966_;
v_entries_3953_ = v___x_3967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3969_, lean_object* v_keys_3970_, lean_object* v_vals_3971_, lean_object* v_i_3972_, lean_object* v_entries_3973_){
_start:
{
size_t v_depth_boxed_3974_; lean_object* v_res_3975_; 
v_depth_boxed_3974_ = lean_unbox_usize(v_depth_3969_);
lean_dec(v_depth_3969_);
v_res_3975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3974_, v_keys_3970_, v_vals_3971_, v_i_3972_, v_entries_3973_);
lean_dec_ref(v_vals_3971_);
lean_dec_ref(v_keys_3970_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3976_, lean_object* v_x_3977_, lean_object* v_x_3978_, lean_object* v_x_3979_, lean_object* v_x_3980_){
_start:
{
size_t v_x_2310__boxed_3981_; size_t v_x_2311__boxed_3982_; lean_object* v_res_3983_; 
v_x_2310__boxed_3981_ = lean_unbox_usize(v_x_3977_);
lean_dec(v_x_3977_);
v_x_2311__boxed_3982_ = lean_unbox_usize(v_x_3978_);
lean_dec(v_x_3978_);
v_res_3983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3976_, v_x_2310__boxed_3981_, v_x_2311__boxed_3982_, v_x_3979_, v_x_3980_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_){
_start:
{
uint64_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; lean_object* v___x_3990_; 
v___x_3987_ = l_Lean_instHashableMVarId_hash(v_x_3985_);
v___x_3988_ = lean_uint64_to_usize(v___x_3987_);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3984_, v___x_3988_, v___x_3989_, v_x_3985_, v_x_3986_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_3991_, lean_object* v_val_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; lean_object* v_mctx_3996_; lean_object* v_cache_3997_; lean_object* v_zetaDeltaFVarIds_3998_; lean_object* v_postponed_3999_; lean_object* v_diag_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4028_; 
v___x_3995_ = lean_st_ref_take(v___y_3993_);
v_mctx_3996_ = lean_ctor_get(v___x_3995_, 0);
v_cache_3997_ = lean_ctor_get(v___x_3995_, 1);
v_zetaDeltaFVarIds_3998_ = lean_ctor_get(v___x_3995_, 2);
v_postponed_3999_ = lean_ctor_get(v___x_3995_, 3);
v_diag_4000_ = lean_ctor_get(v___x_3995_, 4);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4002_ = v___x_3995_;
v_isShared_4003_ = v_isSharedCheck_4028_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_diag_4000_);
lean_inc(v_postponed_3999_);
lean_inc(v_zetaDeltaFVarIds_3998_);
lean_inc(v_cache_3997_);
lean_inc(v_mctx_3996_);
lean_dec(v___x_3995_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4028_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v_depth_4004_; lean_object* v_levelAssignDepth_4005_; lean_object* v_lmvarCounter_4006_; lean_object* v_mvarCounter_4007_; lean_object* v_lDecls_4008_; lean_object* v_decls_4009_; lean_object* v_userNames_4010_; lean_object* v_lAssignment_4011_; lean_object* v_eAssignment_4012_; lean_object* v_dAssignment_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4027_; 
v_depth_4004_ = lean_ctor_get(v_mctx_3996_, 0);
v_levelAssignDepth_4005_ = lean_ctor_get(v_mctx_3996_, 1);
v_lmvarCounter_4006_ = lean_ctor_get(v_mctx_3996_, 2);
v_mvarCounter_4007_ = lean_ctor_get(v_mctx_3996_, 3);
v_lDecls_4008_ = lean_ctor_get(v_mctx_3996_, 4);
v_decls_4009_ = lean_ctor_get(v_mctx_3996_, 5);
v_userNames_4010_ = lean_ctor_get(v_mctx_3996_, 6);
v_lAssignment_4011_ = lean_ctor_get(v_mctx_3996_, 7);
v_eAssignment_4012_ = lean_ctor_get(v_mctx_3996_, 8);
v_dAssignment_4013_ = lean_ctor_get(v_mctx_3996_, 9);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_mctx_3996_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4015_ = v_mctx_3996_;
v_isShared_4016_ = v_isSharedCheck_4027_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_dAssignment_4013_);
lean_inc(v_eAssignment_4012_);
lean_inc(v_lAssignment_4011_);
lean_inc(v_userNames_4010_);
lean_inc(v_decls_4009_);
lean_inc(v_lDecls_4008_);
lean_inc(v_mvarCounter_4007_);
lean_inc(v_lmvarCounter_4006_);
lean_inc(v_levelAssignDepth_4005_);
lean_inc(v_depth_4004_);
lean_dec(v_mctx_3996_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4027_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4019_; 
v___x_4017_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_4012_, v_mvarId_3991_, v_val_3992_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 8, v___x_4017_);
v___x_4019_ = v___x_4015_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_depth_4004_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_levelAssignDepth_4005_);
lean_ctor_set(v_reuseFailAlloc_4026_, 2, v_lmvarCounter_4006_);
lean_ctor_set(v_reuseFailAlloc_4026_, 3, v_mvarCounter_4007_);
lean_ctor_set(v_reuseFailAlloc_4026_, 4, v_lDecls_4008_);
lean_ctor_set(v_reuseFailAlloc_4026_, 5, v_decls_4009_);
lean_ctor_set(v_reuseFailAlloc_4026_, 6, v_userNames_4010_);
lean_ctor_set(v_reuseFailAlloc_4026_, 7, v_lAssignment_4011_);
lean_ctor_set(v_reuseFailAlloc_4026_, 8, v___x_4017_);
lean_ctor_set(v_reuseFailAlloc_4026_, 9, v_dAssignment_4013_);
v___x_4019_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4021_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v___x_4019_);
v___x_4021_ = v___x_4002_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v_cache_3997_);
lean_ctor_set(v_reuseFailAlloc_4025_, 2, v_zetaDeltaFVarIds_3998_);
lean_ctor_set(v_reuseFailAlloc_4025_, 3, v_postponed_3999_);
lean_ctor_set(v_reuseFailAlloc_4025_, 4, v_diag_4000_);
v___x_4021_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = lean_st_ref_set(v___y_3993_, v___x_4021_);
v___x_4023_ = lean_box(0);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4029_, lean_object* v_val_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4029_, v_val_4030_, v___y_4031_);
lean_dec(v___y_4031_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4034_, size_t v_i_4035_, lean_object* v_bs_4036_){
_start:
{
uint8_t v___x_4037_; 
v___x_4037_ = lean_usize_dec_lt(v_i_4035_, v_sz_4034_);
if (v___x_4037_ == 0)
{
return v_bs_4036_;
}
else
{
lean_object* v_v_4038_; lean_object* v___x_4039_; lean_object* v_bs_x27_4040_; lean_object* v___x_4041_; size_t v___x_4042_; size_t v___x_4043_; lean_object* v___x_4044_; 
v_v_4038_ = lean_array_uget(v_bs_4036_, v_i_4035_);
v___x_4039_ = lean_unsigned_to_nat(0u);
v_bs_x27_4040_ = lean_array_uset(v_bs_4036_, v_i_4035_, v___x_4039_);
v___x_4041_ = l_Lean_Expr_fvar___override(v_v_4038_);
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_add(v_i_4035_, v___x_4042_);
v___x_4044_ = lean_array_uset(v_bs_x27_4040_, v_i_4035_, v___x_4041_);
v_i_4035_ = v___x_4043_;
v_bs_4036_ = v___x_4044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4046_, lean_object* v_i_4047_, lean_object* v_bs_4048_){
_start:
{
size_t v_sz_boxed_4049_; size_t v_i_boxed_4050_; lean_object* v_res_4051_; 
v_sz_boxed_4049_ = lean_unbox_usize(v_sz_4046_);
lean_dec(v_sz_4046_);
v_i_boxed_4050_ = lean_unbox_usize(v_i_4047_);
lean_dec(v_i_4047_);
v_res_4051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4049_, v_i_boxed_4050_, v_bs_4048_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4052_, lean_object* v_mvarId_4053_, lean_object* v___x_4054_, lean_object* v_a_4055_, lean_object* v_fvarIds_4056_, lean_object* v_es_4057_, lean_object* v_givenNames_x27_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___y_4116_; lean_object* v___x_4126_; uint8_t v___x_4127_; 
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = lean_array_get_borrowed(v___x_4052_, v_es_4057_, v___x_4064_);
v___x_4126_ = lean_array_get_size(v_fvarIds_4056_);
v___x_4127_ = lean_nat_dec_eq(v___x_4126_, v___x_4064_);
if (v___x_4127_ == 0)
{
v___y_4116_ = v___x_4127_;
goto v___jp_4115_;
}
else
{
uint8_t v___x_4128_; 
v___x_4128_ = lean_expr_eqv(v_a_4055_, v___x_4065_);
v___y_4116_ = v___x_4128_;
goto v___jp_4115_;
}
v___jp_4066_:
{
lean_object* v___x_4067_; 
lean_inc(v_mvarId_4053_);
v___x_4067_ = l_Lean_MVarId_getTag(v_mvarId_4053_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
lean_inc(v___x_4065_);
v___x_4069_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4065_, v_a_4068_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; size_t v_sz_4071_; size_t v___x_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; uint8_t v___x_4075_; uint8_t v___x_4076_; lean_object* v___x_4077_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc_n(v_a_4070_, 2);
lean_dec_ref_known(v___x_4069_, 1);
v_sz_4071_ = lean_array_size(v_fvarIds_4056_);
v___x_4072_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4056_);
v___x_4073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4071_, v___x_4072_, v_fvarIds_4056_);
v___x_4074_ = 0;
v___x_4075_ = 1;
v___x_4076_ = 1;
v___x_4077_ = l_Lean_Meta_mkLetFVars(v___x_4073_, v_a_4070_, v___x_4074_, v___x_4075_, v___x_4076_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec_ref(v___x_4073_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4089_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
v___x_4079_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4053_, v_a_4078_, v___y_4060_);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v___x_4079_, 0);
lean_dec(v_unused_4090_);
v___x_4081_ = v___x_4079_;
v_isShared_4082_ = v_isSharedCheck_4089_;
goto v_resetjp_4080_;
}
else
{
lean_dec(v___x_4079_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4089_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4083_, 0, v_fvarIds_4056_);
lean_ctor_set(v___x_4083_, 1, v_givenNames_x27_4058_);
v___x_4084_ = l_Lean_Expr_mvarId_x21(v_a_4070_);
lean_dec(v_a_4070_);
v___x_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v___x_4085_);
v___x_4087_ = v___x_4081_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec(v_a_4070_);
lean_dec(v_givenNames_x27_4058_);
lean_dec_ref(v_fvarIds_4056_);
lean_dec(v_mvarId_4053_);
v_a_4091_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4077_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4077_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_givenNames_x27_4058_);
lean_dec_ref(v_fvarIds_4056_);
lean_dec(v_mvarId_4053_);
v_a_4099_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4069_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4069_);
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
lean_dec(v_givenNames_x27_4058_);
lean_dec_ref(v_fvarIds_4056_);
lean_dec(v_mvarId_4053_);
v_a_4107_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4067_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4067_);
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
v___jp_4115_:
{
if (v___y_4116_ == 0)
{
lean_dec(v___x_4054_);
goto v___jp_4066_;
}
else
{
lean_object* v___x_4117_; 
lean_inc(v_mvarId_4053_);
v___x_4117_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4054_, v_mvarId_4053_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_dec_ref_known(v___x_4117_, 1);
goto v___jp_4066_;
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v_givenNames_x27_4058_);
lean_dec_ref(v_fvarIds_4056_);
lean_dec(v_mvarId_4053_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4129_, lean_object* v_mvarId_4130_, lean_object* v___x_4131_, lean_object* v_a_4132_, lean_object* v_fvarIds_4133_, lean_object* v_es_4134_, lean_object* v_givenNames_x27_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_MVarId_extractLets___lam__0(v___x_4129_, v_mvarId_4130_, v___x_4131_, v_a_4132_, v_fvarIds_4133_, v_es_4134_, v_givenNames_x27_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec_ref(v_es_4134_);
lean_dec_ref(v_a_4132_);
lean_dec_ref(v___x_4129_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4142_, lean_object* v___x_4143_, lean_object* v___x_4144_, lean_object* v_givenNames_4145_, lean_object* v_config_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___x_4152_; 
lean_inc(v___x_4143_);
lean_inc(v_mvarId_4142_);
v___x_4152_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4142_, v___x_4143_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v___x_4153_; 
lean_dec_ref_known(v___x_4152_, 1);
lean_inc(v_mvarId_4142_);
v___x_4153_ = l_Lean_MVarId_getType(v_mvarId_4142_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc_n(v_a_4154_, 2);
lean_dec_ref_known(v___x_4153_, 1);
v___f_4155_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4155_, 0, v___x_4144_);
lean_closure_set(v___f_4155_, 1, v_mvarId_4142_);
lean_closure_set(v___f_4155_, 2, v___x_4143_);
lean_closure_set(v___f_4155_, 3, v_a_4154_);
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = lean_mk_empty_array_with_capacity(v___x_4156_);
v___x_4158_ = lean_array_push(v___x_4157_, v_a_4154_);
v___x_4159_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4158_, v_givenNames_4145_, v___f_4155_, v_config_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
return v___x_4159_;
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec(v_givenNames_4145_);
lean_dec_ref(v___x_4144_);
lean_dec(v___x_4143_);
lean_dec(v_mvarId_4142_);
v_a_4160_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4153_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4153_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_givenNames_4145_);
lean_dec_ref(v___x_4144_);
lean_dec(v___x_4143_);
lean_dec(v_mvarId_4142_);
v_a_4168_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4152_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4152_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4176_, lean_object* v___x_4177_, lean_object* v___x_4178_, lean_object* v_givenNames_4179_, lean_object* v_config_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4176_, v___x_4177_, v___x_4178_, v_givenNames_4179_, v_config_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec_ref(v_config_4180_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4190_, lean_object* v_givenNames_4191_, lean_object* v_config_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; 
v___x_4198_ = l_Lean_instInhabitedExpr;
v___x_4199_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4190_);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4200_, 0, v_mvarId_4190_);
lean_closure_set(v___f_4200_, 1, v___x_4199_);
lean_closure_set(v___f_4200_, 2, v___x_4198_);
lean_closure_set(v___f_4200_, 3, v_givenNames_4191_);
lean_closure_set(v___f_4200_, 4, v_config_4192_);
v___x_4201_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4190_, v___f_4200_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4202_, lean_object* v_givenNames_4203_, lean_object* v_config_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_MVarId_extractLets(v_mvarId_4202_, v_givenNames_4203_, v_config_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
lean_dec(v_a_4206_);
lean_dec_ref(v_a_4205_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4211_, lean_object* v_val_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4211_, v_val_4212_, v___y_4214_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4219_, lean_object* v_val_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4219_, v_val_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4227_, lean_object* v_x_4228_, lean_object* v_x_4229_, lean_object* v_x_4230_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4228_, v_x_4229_, v_x_4230_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4232_, lean_object* v_x_4233_, size_t v_x_4234_, size_t v_x_4235_, lean_object* v_x_4236_, lean_object* v_x_4237_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4233_, v_x_4234_, v_x_4235_, v_x_4236_, v_x_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4239_, lean_object* v_x_4240_, lean_object* v_x_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_, lean_object* v_x_4244_){
_start:
{
size_t v_x_2808__boxed_4245_; size_t v_x_2809__boxed_4246_; lean_object* v_res_4247_; 
v_x_2808__boxed_4245_ = lean_unbox_usize(v_x_4241_);
lean_dec(v_x_4241_);
v_x_2809__boxed_4246_ = lean_unbox_usize(v_x_4242_);
lean_dec(v_x_4242_);
v_res_4247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4239_, v_x_4240_, v_x_2808__boxed_4245_, v_x_2809__boxed_4246_, v_x_4243_, v_x_4244_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4248_, lean_object* v_n_4249_, lean_object* v_k_4250_, lean_object* v_v_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4249_, v_k_4250_, v_v_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4253_, size_t v_depth_4254_, lean_object* v_keys_4255_, lean_object* v_vals_4256_, lean_object* v_heq_4257_, lean_object* v_i_4258_, lean_object* v_entries_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4254_, v_keys_4255_, v_vals_4256_, v_i_4258_, v_entries_4259_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4261_, lean_object* v_depth_4262_, lean_object* v_keys_4263_, lean_object* v_vals_4264_, lean_object* v_heq_4265_, lean_object* v_i_4266_, lean_object* v_entries_4267_){
_start:
{
size_t v_depth_boxed_4268_; lean_object* v_res_4269_; 
v_depth_boxed_4268_ = lean_unbox_usize(v_depth_4262_);
lean_dec(v_depth_4262_);
v_res_4269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4261_, v_depth_boxed_4268_, v_keys_4263_, v_vals_4264_, v_heq_4265_, v_i_4266_, v_entries_4267_);
lean_dec_ref(v_vals_4264_);
lean_dec_ref(v_keys_4263_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4270_, lean_object* v_x_4271_, lean_object* v_x_4272_, lean_object* v_x_4273_, lean_object* v_x_4274_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4271_, v_x_4272_, v_x_4273_, v_x_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4276_, size_t v_i_4277_, lean_object* v_bs_4278_){
_start:
{
uint8_t v___x_4279_; 
v___x_4279_ = lean_usize_dec_lt(v_i_4277_, v_sz_4276_);
if (v___x_4279_ == 0)
{
return v_bs_4278_;
}
else
{
lean_object* v_v_4280_; lean_object* v___x_4281_; lean_object* v_bs_x27_4282_; lean_object* v___x_4283_; size_t v___x_4284_; size_t v___x_4285_; lean_object* v___x_4286_; 
v_v_4280_ = lean_array_uget(v_bs_4278_, v_i_4277_);
v___x_4281_ = lean_unsigned_to_nat(0u);
v_bs_x27_4282_ = lean_array_uset(v_bs_4278_, v_i_4277_, v___x_4281_);
v___x_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4283_, 0, v_v_4280_);
v___x_4284_ = ((size_t)1ULL);
v___x_4285_ = lean_usize_add(v_i_4277_, v___x_4284_);
v___x_4286_ = lean_array_uset(v_bs_x27_4282_, v_i_4277_, v___x_4283_);
v_i_4277_ = v___x_4285_;
v_bs_4278_ = v___x_4286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4288_, lean_object* v_i_4289_, lean_object* v_bs_4290_){
_start:
{
size_t v_sz_boxed_4291_; size_t v_i_boxed_4292_; lean_object* v_res_4293_; 
v_sz_boxed_4291_ = lean_unbox_usize(v_sz_4288_);
lean_dec(v_sz_4288_);
v_i_boxed_4292_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_res_4293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4291_, v_i_boxed_4292_, v_bs_4290_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4294_, lean_object* v_fvars_4295_, lean_object* v_fvarIds_4296_, lean_object* v_givenNames_x27_4297_, lean_object* v_targetNew_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v___x_4304_; 
lean_inc(v_mvarId_4294_);
v___x_4304_ = l_Lean_MVarId_getTag(v_mvarId_4294_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4306_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4305_);
lean_dec_ref_known(v___x_4304_, 1);
v___x_4306_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4298_, v_a_4305_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; size_t v_sz_4308_; size_t v___x_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; uint8_t v___x_4312_; uint8_t v___x_4313_; lean_object* v___x_4314_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc_n(v_a_4307_, 2);
lean_dec_ref_known(v___x_4306_, 1);
v_sz_4308_ = lean_array_size(v_fvarIds_4296_);
v___x_4309_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4296_);
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4308_, v___x_4309_, v_fvarIds_4296_);
v___x_4311_ = 0;
v___x_4312_ = 1;
v___x_4313_ = 1;
v___x_4314_ = l_Lean_Meta_mkLetFVars(v___x_4310_, v_a_4307_, v___x_4311_, v___x_4312_, v___x_4313_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec_ref(v___x_4310_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4329_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4294_, v_a_4315_, v___y_4300_);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4329_ == 0)
{
lean_object* v_unused_4330_; 
v_unused_4330_ = lean_ctor_get(v___x_4316_, 0);
lean_dec(v_unused_4330_);
v___x_4318_ = v___x_4316_;
v_isShared_4319_ = v_isSharedCheck_4329_;
goto v_resetjp_4317_;
}
else
{
lean_dec(v___x_4316_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4329_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; size_t v_sz_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4327_; 
v___x_4320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4320_, 0, v_fvarIds_4296_);
lean_ctor_set(v___x_4320_, 1, v_givenNames_x27_4297_);
v_sz_4321_ = lean_array_size(v_fvars_4295_);
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4321_, v___x_4309_, v_fvars_4295_);
v___x_4323_ = l_Lean_Expr_mvarId_x21(v_a_4307_);
lean_dec(v_a_4307_);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4320_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v___x_4325_);
v___x_4327_ = v___x_4318_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4325_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_a_4307_);
lean_dec(v_givenNames_x27_4297_);
lean_dec_ref(v_fvarIds_4296_);
lean_dec_ref(v_fvars_4295_);
lean_dec(v_mvarId_4294_);
v_a_4331_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4314_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4314_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_givenNames_x27_4297_);
lean_dec_ref(v_fvarIds_4296_);
lean_dec_ref(v_fvars_4295_);
lean_dec(v_mvarId_4294_);
v_a_4339_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4306_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4306_);
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
lean_dec_ref(v_targetNew_4298_);
lean_dec(v_givenNames_x27_4297_);
lean_dec_ref(v_fvarIds_4296_);
lean_dec_ref(v_fvars_4295_);
lean_dec(v_mvarId_4294_);
v_a_4347_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4304_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4304_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4355_, lean_object* v_fvars_4356_, lean_object* v_fvarIds_4357_, lean_object* v_givenNames_x27_4358_, lean_object* v_targetNew_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4355_, v_fvars_4356_, v_fvarIds_4357_, v_givenNames_x27_4358_, v_targetNew_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4366_, lean_object* v_binderName_4367_, lean_object* v_body_4368_, uint8_t v_binderInfo_4369_, lean_object* v___f_4370_, lean_object* v___x_4371_, lean_object* v_mvarId_4372_, lean_object* v_binderType_4373_, lean_object* v_fvarIds_4374_, lean_object* v_es_4375_, lean_object* v_givenNames_x27_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___y_4388_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v___x_4382_ = lean_unsigned_to_nat(0u);
v___x_4383_ = lean_array_get_borrowed(v___x_4366_, v_es_4375_, v___x_4382_);
v___x_4398_ = lean_array_get_size(v_fvarIds_4374_);
v___x_4399_ = lean_nat_dec_eq(v___x_4398_, v___x_4382_);
if (v___x_4399_ == 0)
{
v___y_4388_ = v___x_4399_;
goto v___jp_4387_;
}
else
{
uint8_t v___x_4400_; 
v___x_4400_ = lean_expr_eqv(v_binderType_4373_, v___x_4383_);
v___y_4388_ = v___x_4400_;
goto v___jp_4387_;
}
v___jp_4384_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_inc(v___x_4383_);
v___x_4385_ = l_Lean_Expr_forallE___override(v_binderName_4367_, v___x_4383_, v_body_4368_, v_binderInfo_4369_);
lean_inc(v___y_4380_);
lean_inc_ref(v___y_4379_);
lean_inc(v___y_4378_);
lean_inc_ref(v___y_4377_);
v___x_4386_ = lean_apply_8(v___f_4370_, v_fvarIds_4374_, v_givenNames_x27_4376_, v___x_4385_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, lean_box(0));
return v___x_4386_;
}
v___jp_4387_:
{
if (v___y_4388_ == 0)
{
lean_dec(v_mvarId_4372_);
lean_dec(v___x_4371_);
goto v___jp_4384_;
}
else
{
lean_object* v___x_4389_; 
v___x_4389_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4371_, v_mvarId_4372_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_dec_ref_known(v___x_4389_, 1);
goto v___jp_4384_;
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_givenNames_x27_4376_);
lean_dec_ref(v_fvarIds_4374_);
lean_dec_ref(v___f_4370_);
lean_dec_ref(v_body_4368_);
lean_dec(v_binderName_4367_);
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4401_, lean_object* v_binderName_4402_, lean_object* v_body_4403_, lean_object* v_binderInfo_4404_, lean_object* v___f_4405_, lean_object* v___x_4406_, lean_object* v_mvarId_4407_, lean_object* v_binderType_4408_, lean_object* v_fvarIds_4409_, lean_object* v_es_4410_, lean_object* v_givenNames_x27_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
uint8_t v_binderInfo_1854__boxed_4417_; lean_object* v_res_4418_; 
v_binderInfo_1854__boxed_4417_ = lean_unbox(v_binderInfo_4404_);
v_res_4418_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4401_, v_binderName_4402_, v_body_4403_, v_binderInfo_1854__boxed_4417_, v___f_4405_, v___x_4406_, v_mvarId_4407_, v_binderType_4408_, v_fvarIds_4409_, v_es_4410_, v_givenNames_x27_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec_ref(v_es_4410_);
lean_dec_ref(v_binderType_4408_);
lean_dec_ref(v___x_4401_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4419_, lean_object* v_declName_4420_, lean_object* v_body_4421_, uint8_t v_nondep_4422_, lean_object* v___f_4423_, lean_object* v_value_4424_, lean_object* v___x_4425_, lean_object* v_mvarId_4426_, lean_object* v_type_4427_, lean_object* v_fvarIds_4428_, lean_object* v_es_4429_, lean_object* v_givenNames_x27_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; uint8_t v___y_4444_; lean_object* v___x_4455_; uint8_t v___x_4456_; 
v___x_4436_ = lean_unsigned_to_nat(0u);
v___x_4437_ = lean_array_get_borrowed(v___x_4419_, v_es_4429_, v___x_4436_);
v___x_4438_ = lean_unsigned_to_nat(1u);
v___x_4439_ = lean_array_get_borrowed(v___x_4419_, v_es_4429_, v___x_4438_);
v___x_4455_ = lean_array_get_size(v_fvarIds_4428_);
v___x_4456_ = lean_nat_dec_eq(v___x_4455_, v___x_4436_);
if (v___x_4456_ == 0)
{
v___y_4444_ = v___x_4456_;
goto v___jp_4443_;
}
else
{
uint8_t v___x_4457_; 
v___x_4457_ = lean_expr_eqv(v_type_4427_, v___x_4437_);
v___y_4444_ = v___x_4457_;
goto v___jp_4443_;
}
v___jp_4440_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_inc(v___x_4439_);
lean_inc(v___x_4437_);
v___x_4441_ = l_Lean_Expr_letE___override(v_declName_4420_, v___x_4437_, v___x_4439_, v_body_4421_, v_nondep_4422_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
lean_inc(v___y_4432_);
lean_inc_ref(v___y_4431_);
v___x_4442_ = lean_apply_8(v___f_4423_, v_fvarIds_4428_, v_givenNames_x27_4430_, v___x_4441_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, lean_box(0));
return v___x_4442_;
}
v___jp_4443_:
{
if (v___y_4444_ == 0)
{
lean_dec(v_mvarId_4426_);
lean_dec(v___x_4425_);
goto v___jp_4440_;
}
else
{
uint8_t v___x_4445_; 
v___x_4445_ = lean_expr_eqv(v_value_4424_, v___x_4439_);
if (v___x_4445_ == 0)
{
lean_dec(v_mvarId_4426_);
lean_dec(v___x_4425_);
goto v___jp_4440_;
}
else
{
lean_object* v___x_4446_; 
v___x_4446_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4425_, v_mvarId_4426_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_dec_ref_known(v___x_4446_, 1);
goto v___jp_4440_;
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v_givenNames_x27_4430_);
lean_dec_ref(v_fvarIds_4428_);
lean_dec_ref(v___f_4423_);
lean_dec_ref(v_body_4421_);
lean_dec(v_declName_4420_);
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4458_ = _args[0];
lean_object* v_declName_4459_ = _args[1];
lean_object* v_body_4460_ = _args[2];
lean_object* v_nondep_4461_ = _args[3];
lean_object* v___f_4462_ = _args[4];
lean_object* v_value_4463_ = _args[5];
lean_object* v___x_4464_ = _args[6];
lean_object* v_mvarId_4465_ = _args[7];
lean_object* v_type_4466_ = _args[8];
lean_object* v_fvarIds_4467_ = _args[9];
lean_object* v_es_4468_ = _args[10];
lean_object* v_givenNames_x27_4469_ = _args[11];
lean_object* v___y_4470_ = _args[12];
lean_object* v___y_4471_ = _args[13];
lean_object* v___y_4472_ = _args[14];
lean_object* v___y_4473_ = _args[15];
lean_object* v___y_4474_ = _args[16];
_start:
{
uint8_t v_nondep_1929__boxed_4475_; lean_object* v_res_4476_; 
v_nondep_1929__boxed_4475_ = lean_unbox(v_nondep_4461_);
v_res_4476_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4458_, v_declName_4459_, v_body_4460_, v_nondep_1929__boxed_4475_, v___f_4462_, v_value_4463_, v___x_4464_, v_mvarId_4465_, v_type_4466_, v_fvarIds_4467_, v_es_4468_, v_givenNames_x27_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec_ref(v_es_4468_);
lean_dec_ref(v_type_4466_);
lean_dec_ref(v_value_4463_);
lean_dec_ref(v___x_4458_);
return v_res_4476_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4481_ = l_Lean_MessageData_ofFormat(v___x_4480_);
return v___x_4481_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4484_, lean_object* v___x_4485_, lean_object* v___f_4486_, lean_object* v___x_4487_, lean_object* v_givenNames_4488_, lean_object* v_config_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
lean_inc(v_mvarId_4484_);
v___x_4495_ = l_Lean_MVarId_getType(v_mvarId_4484_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
switch(lean_obj_tag(v_a_4496_))
{
case 7:
{
lean_object* v_binderName_4497_; lean_object* v_binderType_4498_; lean_object* v_body_4499_; uint8_t v_binderInfo_4500_; lean_object* v___x_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v_binderName_4497_ = lean_ctor_get(v_a_4496_, 0);
lean_inc(v_binderName_4497_);
v_binderType_4498_ = lean_ctor_get(v_a_4496_, 1);
lean_inc_ref_n(v_binderType_4498_, 2);
v_body_4499_ = lean_ctor_get(v_a_4496_, 2);
lean_inc_ref(v_body_4499_);
v_binderInfo_4500_ = lean_ctor_get_uint8(v_a_4496_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4496_, 3);
v___x_4501_ = lean_box(v_binderInfo_4500_);
v___f_4502_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4502_, 0, v___x_4485_);
lean_closure_set(v___f_4502_, 1, v_binderName_4497_);
lean_closure_set(v___f_4502_, 2, v_body_4499_);
lean_closure_set(v___f_4502_, 3, v___x_4501_);
lean_closure_set(v___f_4502_, 4, v___f_4486_);
lean_closure_set(v___f_4502_, 5, v___x_4487_);
lean_closure_set(v___f_4502_, 6, v_mvarId_4484_);
lean_closure_set(v___f_4502_, 7, v_binderType_4498_);
v___x_4503_ = lean_unsigned_to_nat(1u);
v___x_4504_ = lean_mk_empty_array_with_capacity(v___x_4503_);
v___x_4505_ = lean_array_push(v___x_4504_, v_binderType_4498_);
v___x_4506_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4505_, v_givenNames_4488_, v___f_4502_, v_config_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4506_;
}
case 8:
{
lean_object* v_declName_4507_; lean_object* v_type_4508_; lean_object* v_value_4509_; lean_object* v_body_4510_; uint8_t v_nondep_4511_; lean_object* v___x_4512_; lean_object* v___f_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_declName_4507_ = lean_ctor_get(v_a_4496_, 0);
lean_inc(v_declName_4507_);
v_type_4508_ = lean_ctor_get(v_a_4496_, 1);
lean_inc_ref_n(v_type_4508_, 2);
v_value_4509_ = lean_ctor_get(v_a_4496_, 2);
lean_inc_ref_n(v_value_4509_, 2);
v_body_4510_ = lean_ctor_get(v_a_4496_, 3);
lean_inc_ref(v_body_4510_);
v_nondep_4511_ = lean_ctor_get_uint8(v_a_4496_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4496_, 4);
v___x_4512_ = lean_box(v_nondep_4511_);
v___f_4513_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4513_, 0, v___x_4485_);
lean_closure_set(v___f_4513_, 1, v_declName_4507_);
lean_closure_set(v___f_4513_, 2, v_body_4510_);
lean_closure_set(v___f_4513_, 3, v___x_4512_);
lean_closure_set(v___f_4513_, 4, v___f_4486_);
lean_closure_set(v___f_4513_, 5, v_value_4509_);
lean_closure_set(v___f_4513_, 6, v___x_4487_);
lean_closure_set(v___f_4513_, 7, v_mvarId_4484_);
lean_closure_set(v___f_4513_, 8, v_type_4508_);
v___x_4514_ = lean_unsigned_to_nat(2u);
v___x_4515_ = lean_mk_empty_array_with_capacity(v___x_4514_);
v___x_4516_ = lean_array_push(v___x_4515_, v_type_4508_);
v___x_4517_ = lean_array_push(v___x_4516_, v_value_4509_);
v___x_4518_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4517_, v_givenNames_4488_, v___f_4513_, v_config_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4518_;
}
default: 
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
lean_dec(v_a_4496_);
lean_dec(v_givenNames_4488_);
lean_dec_ref(v___f_4486_);
lean_dec_ref(v___x_4485_);
v___x_4519_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4520_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4487_, v_mvarId_4484_, v___x_4519_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4520_;
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_givenNames_4488_);
lean_dec(v___x_4487_);
lean_dec_ref(v___f_4486_);
lean_dec_ref(v___x_4485_);
lean_dec(v_mvarId_4484_);
v_a_4521_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4495_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4495_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4529_, lean_object* v___x_4530_, lean_object* v___f_4531_, lean_object* v___x_4532_, lean_object* v_givenNames_4533_, lean_object* v_config_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4529_, v___x_4530_, v___f_4531_, v___x_4532_, v_givenNames_4533_, v_config_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec_ref(v_config_4534_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4541_, lean_object* v___x_4542_, lean_object* v_givenNames_4543_, lean_object* v_config_4544_, lean_object* v_mvarId_4545_, lean_object* v_fvars_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___f_4552_; lean_object* v___f_4553_; lean_object* v___x_4554_; 
lean_inc_n(v_mvarId_4545_, 2);
v___f_4552_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4552_, 0, v_mvarId_4545_);
lean_closure_set(v___f_4552_, 1, v_fvars_4546_);
v___f_4553_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4553_, 0, v_mvarId_4545_);
lean_closure_set(v___f_4553_, 1, v___x_4541_);
lean_closure_set(v___f_4553_, 2, v___f_4552_);
lean_closure_set(v___f_4553_, 3, v___x_4542_);
lean_closure_set(v___f_4553_, 4, v_givenNames_4543_);
lean_closure_set(v___f_4553_, 5, v_config_4544_);
v___x_4554_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4545_, v___f_4553_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4555_, lean_object* v___x_4556_, lean_object* v_givenNames_4557_, lean_object* v_config_4558_, lean_object* v_mvarId_4559_, lean_object* v_fvars_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4555_, v___x_4556_, v_givenNames_4557_, v_config_4558_, v_mvarId_4559_, v_fvars_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4567_, lean_object* v_fvarId_4568_, lean_object* v_givenNames_4569_, lean_object* v_config_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4567_);
v___x_4577_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4567_, v___x_4576_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v___x_4578_; lean_object* v___f_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; uint8_t v___x_4583_; lean_object* v___x_4584_; 
lean_dec_ref_known(v___x_4577_, 1);
v___x_4578_ = l_Lean_instInhabitedExpr;
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4579_, 0, v___x_4578_);
lean_closure_set(v___f_4579_, 1, v___x_4576_);
lean_closure_set(v___f_4579_, 2, v_givenNames_4569_);
lean_closure_set(v___f_4579_, 3, v_config_4570_);
v___x_4580_ = lean_unsigned_to_nat(1u);
v___x_4581_ = lean_mk_empty_array_with_capacity(v___x_4580_);
v___x_4582_ = lean_array_push(v___x_4581_, v_fvarId_4568_);
v___x_4583_ = 0;
v___x_4584_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4567_, v___x_4582_, v___f_4579_, v___x_4583_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4584_;
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_config_4570_);
lean_dec(v_givenNames_4569_);
lean_dec(v_fvarId_4568_);
lean_dec(v_mvarId_4567_);
v_a_4585_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4577_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4577_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4593_, lean_object* v_fvarId_4594_, lean_object* v_givenNames_4595_, lean_object* v_config_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4593_, v_fvarId_4594_, v_givenNames_4595_, v_config_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4603_, lean_object* v___x_4604_, lean_object* v_config_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; 
lean_inc(v___x_4604_);
lean_inc(v_mvarId_4603_);
v___x_4611_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4603_, v___x_4604_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v___x_4612_; 
lean_dec_ref_known(v___x_4611_, 1);
lean_inc(v_mvarId_4603_);
v___x_4612_ = l_Lean_MVarId_getType(v_mvarId_4603_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4614_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc_n(v_a_4613_, 2);
lean_dec_ref_known(v___x_4612_, 1);
v___x_4614_ = l_Lean_Meta_liftLets(v_a_4613_, v_config_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; uint8_t v___x_4616_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref_known(v___x_4614_, 1);
v___x_4616_ = lean_expr_eqv(v_a_4613_, v_a_4615_);
lean_dec(v_a_4613_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
lean_dec(v___x_4604_);
v___x_4617_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4603_, v_a_4615_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
return v___x_4617_;
}
else
{
lean_object* v___x_4618_; 
lean_inc(v_mvarId_4603_);
v___x_4618_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4604_, v_mvarId_4603_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v___x_4619_; 
lean_dec_ref_known(v___x_4618_, 1);
v___x_4619_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4603_, v_a_4615_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
return v___x_4619_;
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_dec(v_a_4615_);
lean_dec(v_mvarId_4603_);
v_a_4620_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4618_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4618_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec(v_a_4613_);
lean_dec(v___x_4604_);
lean_dec(v_mvarId_4603_);
v_a_4628_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4614_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4614_);
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
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec_ref(v_config_4605_);
lean_dec(v___x_4604_);
lean_dec(v_mvarId_4603_);
v_a_4636_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4612_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4612_);
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
lean_dec_ref(v_config_4605_);
lean_dec(v___x_4604_);
lean_dec(v_mvarId_4603_);
v_a_4644_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4611_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4611_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4652_, lean_object* v___x_4653_, lean_object* v_config_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
lean_object* v_res_4660_; 
v_res_4660_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4652_, v___x_4653_, v_config_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4664_, lean_object* v_config_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v___x_4671_; lean_object* v___f_4672_; lean_object* v___x_4673_; 
v___x_4671_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4664_);
v___f_4672_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4672_, 0, v_mvarId_4664_);
lean_closure_set(v___f_4672_, 1, v___x_4671_);
lean_closure_set(v___f_4672_, 2, v_config_4665_);
v___x_4673_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4664_, v___f_4672_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4674_, lean_object* v_config_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l_Lean_MVarId_liftLets(v_mvarId_4674_, v_config_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4682_, lean_object* v_fvars_4683_, lean_object* v_targetNew_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4682_, v_targetNew_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4704_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4693_ = v___x_4690_;
v_isShared_4694_ = v_isSharedCheck_4704_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4690_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4704_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; size_t v_sz_4696_; size_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; 
v___x_4695_ = lean_box(0);
v_sz_4696_ = lean_array_size(v_fvars_4683_);
v___x_4697_ = ((size_t)0ULL);
v___x_4698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4696_, v___x_4697_, v_fvars_4683_);
v___x_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
lean_ctor_set(v___x_4699_, 1, v_a_4691_);
v___x_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4695_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v___x_4700_);
v___x_4702_ = v___x_4693_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4700_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref(v_fvars_4683_);
v_a_4705_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4690_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4690_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4713_, lean_object* v_fvars_4714_, lean_object* v_targetNew_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4713_, v_fvars_4714_, v_targetNew_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4722_, lean_object* v_config_4723_, lean_object* v___f_4724_, lean_object* v___x_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v___x_4731_; 
lean_inc(v_mvarId_4722_);
v___x_4731_ = l_Lean_MVarId_getType(v_mvarId_4722_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref_known(v___x_4731_, 1);
switch(lean_obj_tag(v_a_4732_))
{
case 7:
{
lean_object* v_binderName_4733_; lean_object* v_binderType_4734_; lean_object* v_body_4735_; uint8_t v_binderInfo_4736_; lean_object* v___x_4737_; 
v_binderName_4733_ = lean_ctor_get(v_a_4732_, 0);
lean_inc(v_binderName_4733_);
v_binderType_4734_ = lean_ctor_get(v_a_4732_, 1);
lean_inc_ref_n(v_binderType_4734_, 2);
v_body_4735_ = lean_ctor_get(v_a_4732_, 2);
lean_inc_ref(v_body_4735_);
v_binderInfo_4736_ = lean_ctor_get_uint8(v_a_4732_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4732_, 3);
v___x_4737_ = l_Lean_Meta_liftLets(v_binderType_4734_, v_config_4723_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___y_4740_; lean_object* v___y_4741_; lean_object* v___y_4742_; lean_object* v___y_4743_; uint8_t v___x_4746_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v___x_4746_ = lean_expr_eqv(v_binderType_4734_, v_a_4738_);
lean_dec_ref(v_binderType_4734_);
if (v___x_4746_ == 0)
{
lean_dec(v___x_4725_);
lean_dec(v_mvarId_4722_);
v___y_4740_ = v___y_4726_;
v___y_4741_ = v___y_4727_;
v___y_4742_ = v___y_4728_;
v___y_4743_ = v___y_4729_;
goto v___jp_4739_;
}
else
{
lean_object* v___x_4747_; 
v___x_4747_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4725_, v_mvarId_4722_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_dec_ref_known(v___x_4747_, 1);
v___y_4740_ = v___y_4726_;
v___y_4741_ = v___y_4727_;
v___y_4742_ = v___y_4728_;
v___y_4743_ = v___y_4729_;
goto v___jp_4739_;
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
lean_dec(v_a_4738_);
lean_dec_ref(v_body_4735_);
lean_dec(v_binderName_4733_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec_ref(v___f_4724_);
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4747_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4747_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
v___jp_4739_:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = l_Lean_Expr_forallE___override(v_binderName_4733_, v_a_4738_, v_body_4735_, v_binderInfo_4736_);
v___x_4745_ = lean_apply_6(v___f_4724_, v___x_4744_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, lean_box(0));
return v___x_4745_;
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec_ref(v_body_4735_);
lean_dec_ref(v_binderType_4734_);
lean_dec(v_binderName_4733_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___x_4725_);
lean_dec_ref(v___f_4724_);
lean_dec(v_mvarId_4722_);
v_a_4756_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4737_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4737_);
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
case 8:
{
lean_object* v_declName_4764_; lean_object* v_type_4765_; lean_object* v_value_4766_; lean_object* v_body_4767_; uint8_t v_nondep_4768_; lean_object* v___x_4769_; 
v_declName_4764_ = lean_ctor_get(v_a_4732_, 0);
lean_inc(v_declName_4764_);
v_type_4765_ = lean_ctor_get(v_a_4732_, 1);
lean_inc_ref_n(v_type_4765_, 2);
v_value_4766_ = lean_ctor_get(v_a_4732_, 2);
lean_inc_ref(v_value_4766_);
v_body_4767_ = lean_ctor_get(v_a_4732_, 3);
lean_inc_ref(v_body_4767_);
v_nondep_4768_ = lean_ctor_get_uint8(v_a_4732_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4732_, 4);
lean_inc_ref(v_config_4723_);
v___x_4769_ = l_Lean_Meta_liftLets(v_type_4765_, v_config_4723_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4771_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4769_, 1);
lean_inc_ref(v_value_4766_);
v___x_4771_ = l_Lean_Meta_liftLets(v_value_4766_, v_config_4723_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; lean_object* v___y_4777_; uint8_t v___y_4781_; uint8_t v___x_4791_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v___x_4771_, 1);
v___x_4791_ = lean_expr_eqv(v_type_4765_, v_a_4770_);
lean_dec_ref(v_type_4765_);
if (v___x_4791_ == 0)
{
lean_dec_ref(v_value_4766_);
v___y_4781_ = v___x_4791_;
goto v___jp_4780_;
}
else
{
uint8_t v___x_4792_; 
v___x_4792_ = lean_expr_eqv(v_value_4766_, v_a_4772_);
lean_dec_ref(v_value_4766_);
v___y_4781_ = v___x_4792_;
goto v___jp_4780_;
}
v___jp_4773_:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4778_ = l_Lean_Expr_letE___override(v_declName_4764_, v_a_4770_, v_a_4772_, v_body_4767_, v_nondep_4768_);
v___x_4779_ = lean_apply_6(v___f_4724_, v___x_4778_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, lean_box(0));
return v___x_4779_;
}
v___jp_4780_:
{
if (v___y_4781_ == 0)
{
lean_dec(v___x_4725_);
lean_dec(v_mvarId_4722_);
v___y_4774_ = v___y_4726_;
v___y_4775_ = v___y_4727_;
v___y_4776_ = v___y_4728_;
v___y_4777_ = v___y_4729_;
goto v___jp_4773_;
}
else
{
lean_object* v___x_4782_; 
v___x_4782_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4725_, v_mvarId_4722_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_dec_ref_known(v___x_4782_, 1);
v___y_4774_ = v___y_4726_;
v___y_4775_ = v___y_4727_;
v___y_4776_ = v___y_4728_;
v___y_4777_ = v___y_4729_;
goto v___jp_4773_;
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_dec(v_a_4772_);
lean_dec(v_a_4770_);
lean_dec_ref(v_body_4767_);
lean_dec(v_declName_4764_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec_ref(v___f_4724_);
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4782_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4782_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v_a_4770_);
lean_dec_ref(v_body_4767_);
lean_dec_ref(v_value_4766_);
lean_dec_ref(v_type_4765_);
lean_dec(v_declName_4764_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___x_4725_);
lean_dec_ref(v___f_4724_);
lean_dec(v_mvarId_4722_);
v_a_4793_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4771_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4771_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec_ref(v_body_4767_);
lean_dec_ref(v_value_4766_);
lean_dec_ref(v_type_4765_);
lean_dec(v_declName_4764_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___x_4725_);
lean_dec_ref(v___f_4724_);
lean_dec_ref(v_config_4723_);
lean_dec(v_mvarId_4722_);
v_a_4801_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4769_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4769_);
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
default: 
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
lean_dec(v_a_4732_);
lean_dec_ref(v___f_4724_);
lean_dec_ref(v_config_4723_);
v___x_4809_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4810_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4725_, v_mvarId_4722_, v___x_4809_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
return v___x_4810_;
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___x_4725_);
lean_dec_ref(v___f_4724_);
lean_dec_ref(v_config_4723_);
lean_dec(v_mvarId_4722_);
v_a_4811_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4731_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4731_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4819_, lean_object* v_config_4820_, lean_object* v___f_4821_, lean_object* v___x_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4819_, v_config_4820_, v___f_4821_, v___x_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4829_, lean_object* v___x_4830_, lean_object* v_mvarId_4831_, lean_object* v_fvars_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v___f_4838_; lean_object* v___f_4839_; lean_object* v___x_4840_; 
lean_inc_n(v_mvarId_4831_, 2);
v___f_4838_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4838_, 0, v_mvarId_4831_);
lean_closure_set(v___f_4838_, 1, v_fvars_4832_);
v___f_4839_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4839_, 0, v_mvarId_4831_);
lean_closure_set(v___f_4839_, 1, v_config_4829_);
lean_closure_set(v___f_4839_, 2, v___f_4838_);
lean_closure_set(v___f_4839_, 3, v___x_4830_);
v___x_4840_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4831_, v___f_4839_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4841_, lean_object* v___x_4842_, lean_object* v_mvarId_4843_, lean_object* v_fvars_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4841_, v___x_4842_, v_mvarId_4843_, v_fvars_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4851_, lean_object* v_fvarId_4852_, lean_object* v_config_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4851_);
v___x_4860_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4851_, v___x_4859_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v___f_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; lean_object* v___x_4866_; 
lean_dec_ref_known(v___x_4860_, 1);
v___f_4861_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4861_, 0, v_config_4853_);
lean_closure_set(v___f_4861_, 1, v___x_4859_);
v___x_4862_ = lean_unsigned_to_nat(1u);
v___x_4863_ = lean_mk_empty_array_with_capacity(v___x_4862_);
v___x_4864_ = lean_array_push(v___x_4863_, v_fvarId_4852_);
v___x_4865_ = 0;
v___x_4866_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4851_, v___x_4864_, v___f_4861_, v___x_4865_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4875_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4875_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4875_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v_snd_4871_; lean_object* v___x_4873_; 
v_snd_4871_ = lean_ctor_get(v_a_4867_, 1);
lean_inc(v_snd_4871_);
lean_dec(v_a_4867_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v_snd_4871_);
v___x_4873_ = v___x_4869_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_snd_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
v_a_4876_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4866_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4866_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_dec_ref(v_config_4853_);
lean_dec(v_fvarId_4852_);
lean_dec(v_mvarId_4851_);
v_a_4884_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4860_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4860_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4892_, lean_object* v_fvarId_4893_, lean_object* v_config_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4892_, v_fvarId_4893_, v_config_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_);
lean_dec(v_a_4898_);
lean_dec_ref(v_a_4897_);
lean_dec(v_a_4896_);
lean_dec_ref(v_a_4895_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4901_, lean_object* v___x_4902_, uint8_t v_failIfUnchanged_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v___x_4909_; 
lean_inc(v___x_4902_);
lean_inc(v_mvarId_4901_);
v___x_4909_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4901_, v___x_4902_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4910_; 
lean_dec_ref_known(v___x_4909_, 1);
lean_inc(v_mvarId_4901_);
v___x_4910_ = l_Lean_MVarId_getType(v_mvarId_4901_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc_n(v_a_4911_, 2);
lean_dec_ref_known(v___x_4910_, 1);
v___x_4912_ = l_Lean_Meta_letToHave(v_a_4911_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4912_) == 0)
{
if (v_failIfUnchanged_4903_ == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; 
lean_dec(v_a_4911_);
lean_dec(v___x_4902_);
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4901_, v_a_4913_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
return v___x_4914_;
}
else
{
lean_object* v_a_4915_; uint8_t v___x_4916_; 
v_a_4915_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4916_ = lean_expr_eqv(v_a_4911_, v_a_4915_);
lean_dec(v_a_4911_);
if (v___x_4916_ == 0)
{
lean_object* v___x_4917_; 
lean_dec(v___x_4902_);
v___x_4917_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4901_, v_a_4915_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
return v___x_4917_;
}
else
{
lean_object* v___x_4918_; 
lean_inc(v_mvarId_4901_);
v___x_4918_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4902_, v_mvarId_4901_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v___x_4919_; 
lean_dec_ref_known(v___x_4918_, 1);
v___x_4919_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4901_, v_a_4915_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
return v___x_4919_;
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
lean_dec(v_a_4915_);
lean_dec(v_mvarId_4901_);
v_a_4920_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4918_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4918_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_dec(v_a_4911_);
lean_dec(v___x_4902_);
lean_dec(v_mvarId_4901_);
v_a_4928_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4912_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4912_);
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
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
lean_dec(v___x_4902_);
lean_dec(v_mvarId_4901_);
v_a_4936_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4910_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4910_);
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
lean_dec(v___x_4902_);
lean_dec(v_mvarId_4901_);
v_a_4944_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4946_ = v___x_4909_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4909_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4952_, lean_object* v___x_4953_, lean_object* v_failIfUnchanged_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4960_; lean_object* v_res_4961_; 
v_failIfUnchanged_boxed_4960_ = lean_unbox(v_failIfUnchanged_4954_);
v_res_4961_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4952_, v___x_4953_, v_failIfUnchanged_boxed_4960_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4965_, uint8_t v_failIfUnchanged_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___f_4974_; lean_object* v___x_4975_; 
v___x_4972_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4973_ = lean_box(v_failIfUnchanged_4966_);
lean_inc(v_mvarId_4965_);
v___f_4974_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4974_, 0, v_mvarId_4965_);
lean_closure_set(v___f_4974_, 1, v___x_4972_);
lean_closure_set(v___f_4974_, 2, v___x_4973_);
v___x_4975_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4965_, v___f_4974_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4976_, lean_object* v_failIfUnchanged_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4983_; lean_object* v_res_4984_; 
v_failIfUnchanged_boxed_4983_ = lean_unbox(v_failIfUnchanged_4977_);
v_res_4984_ = l_Lean_MVarId_letToHave(v_mvarId_4976_, v_failIfUnchanged_boxed_4983_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4985_, lean_object* v___x_4986_, lean_object* v_fvarId_4987_, uint8_t v_failIfUnchanged_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; 
lean_inc(v___x_4986_);
lean_inc(v_mvarId_4985_);
v___x_4994_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4985_, v___x_4986_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v___x_4995_; 
lean_dec_ref_known(v___x_4994_, 1);
lean_inc(v_fvarId_4987_);
v___x_4995_ = l_Lean_FVarId_getType___redArg(v_fvarId_4987_, v___y_4989_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4997_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc_n(v_a_4996_, 2);
lean_dec_ref_known(v___x_4995_, 1);
v___x_4997_ = l_Lean_Meta_letToHave(v_a_4996_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_4997_) == 0)
{
if (v_failIfUnchanged_4988_ == 0)
{
lean_object* v_a_4998_; lean_object* v___x_4999_; 
lean_dec(v_a_4996_);
lean_dec(v___x_4986_);
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
lean_inc(v_a_4998_);
lean_dec_ref_known(v___x_4997_, 1);
v___x_4999_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4985_, v_fvarId_4987_, v_a_4998_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
return v___x_4999_;
}
else
{
lean_object* v_a_5000_; uint8_t v___x_5001_; 
v_a_5000_ = lean_ctor_get(v___x_4997_, 0);
lean_inc(v_a_5000_);
lean_dec_ref_known(v___x_4997_, 1);
v___x_5001_ = lean_expr_eqv(v_a_4996_, v_a_5000_);
lean_dec(v_a_4996_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; 
lean_dec(v___x_4986_);
v___x_5002_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4985_, v_fvarId_4987_, v_a_5000_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
return v___x_5002_;
}
else
{
lean_object* v___x_5003_; 
lean_inc(v_mvarId_4985_);
v___x_5003_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4986_, v_mvarId_4985_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v___x_5004_; 
lean_dec_ref_known(v___x_5003_, 1);
v___x_5004_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4985_, v_fvarId_4987_, v_a_5000_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
return v___x_5004_;
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
lean_dec(v_a_5000_);
lean_dec(v_fvarId_4987_);
lean_dec(v_mvarId_4985_);
v_a_5005_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_5003_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_5003_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
}
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec(v_a_4996_);
lean_dec(v_fvarId_4987_);
lean_dec(v___x_4986_);
lean_dec(v_mvarId_4985_);
v_a_5013_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_4997_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_4997_);
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
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_fvarId_4987_);
lean_dec(v___x_4986_);
lean_dec(v_mvarId_4985_);
v_a_5021_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_4995_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_4995_);
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
lean_dec(v_fvarId_4987_);
lean_dec(v___x_4986_);
lean_dec(v_mvarId_4985_);
v_a_5029_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_4994_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_4994_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5037_, lean_object* v___x_5038_, lean_object* v_fvarId_5039_, lean_object* v_failIfUnchanged_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5046_; lean_object* v_res_5047_; 
v_failIfUnchanged_boxed_5046_ = lean_unbox(v_failIfUnchanged_5040_);
v_res_5047_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5037_, v___x_5038_, v_fvarId_5039_, v_failIfUnchanged_boxed_5046_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5048_, lean_object* v_fvarId_5049_, uint8_t v_failIfUnchanged_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___f_5058_; lean_object* v___x_5059_; 
v___x_5056_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5057_ = lean_box(v_failIfUnchanged_5050_);
lean_inc(v_mvarId_5048_);
v___f_5058_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5058_, 0, v_mvarId_5048_);
lean_closure_set(v___f_5058_, 1, v___x_5056_);
lean_closure_set(v___f_5058_, 2, v_fvarId_5049_);
lean_closure_set(v___f_5058_, 3, v___x_5057_);
v___x_5059_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5048_, v___f_5058_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5060_, lean_object* v_fvarId_5061_, lean_object* v_failIfUnchanged_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5068_; lean_object* v_res_5069_; 
v_failIfUnchanged_boxed_5068_ = lean_unbox(v_failIfUnchanged_5062_);
v_res_5069_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5060_, v_fvarId_5061_, v_failIfUnchanged_boxed_5068_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
return v_res_5069_;
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
