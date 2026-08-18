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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__4;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__6_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__7 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__7_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2;
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
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v_cellCount_5_; lean_object* v___x_6_; 
v_cellCount_5_ = lean_unsigned_to_nat(16u);
v___x_6_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2, &l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2);
v___x_8_ = lean_obj_once(&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1, &l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3, &l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3);
v___x_12_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_11_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState_default(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__4, &l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__4);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_instInhabitedState(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_ExtractLets_instInhabitedState_default;
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg(lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_20_; uint8_t v_onlyGivenNames_21_; 
v___x_20_ = lean_st_ref_get(v_a_18_);
v_onlyGivenNames_21_ = lean_ctor_get_uint8(v_a_17_, 8);
if (v_onlyGivenNames_21_ == 0)
{
uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v___x_20_);
v___x_22_ = 1;
v___x_23_ = lean_box(v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
return v___x_24_;
}
else
{
lean_object* v_givenNames_25_; uint8_t v___x_26_; 
v_givenNames_25_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_givenNames_25_);
lean_dec(v___x_20_);
v___x_26_ = l_List_isEmpty___redArg(v_givenNames_25_);
lean_dec(v_givenNames_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_box(v_onlyGivenNames_21_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
else
{
uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = 0;
v___x_30_ = lean_box(v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName___redArg___boxed(lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_hasNextName(lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_36_, v_a_38_);
return v___x_44_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg(lean_object* v_a_59_, lean_object* v_a_60_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___redArg___boxed(lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_84_, v_a_85_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f(lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_88_, v_a_90_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextName_x3f___boxed(lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_ExtractLets_nextName_x3f(v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(lean_object* v_binderName_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_a_116_; 
v___x_115_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_110_, v_a_111_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
if (lean_obj_tag(v_a_116_) == 1)
{
lean_object* v_val_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_167_; 
v_val_117_ = lean_ctor_get(v_a_116_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_a_116_);
if (v_isSharedCheck_167_ == 0)
{
v___x_119_ = v_a_116_;
v_isShared_120_ = v_isSharedCheck_167_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_val_117_);
lean_dec(v_a_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_167_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1));
v___x_122_ = lean_name_eq(v_val_117_, v___x_121_);
if (v___x_122_ == 0)
{
lean_del_object(v___x_119_);
lean_dec(v_val_117_);
lean_dec(v_binderName_109_);
return v___x_115_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_Name_isAnonymous(v_binderName_109_);
if (v___x_123_ == 0)
{
uint8_t v_preserveBinderNames_124_; 
v_preserveBinderNames_124_ = lean_ctor_get_uint8(v_a_110_, 9);
if (v_preserveBinderNames_124_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = l_Lean_Name_hasMacroScopes(v_val_117_);
lean_dec(v_val_117_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec_ref(v___x_115_);
v___x_126_ = l_Lean_Core_mkFreshUserName(v_binderName_109_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_137_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_137_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v_a_127_);
v___x_132_ = v___x_119_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_136_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_132_);
v___x_134_ = v___x_129_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_del_object(v___x_119_);
v_a_138_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_126_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_126_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_del_object(v___x_119_);
lean_dec(v_binderName_109_);
return v___x_115_;
}
}
else
{
lean_del_object(v___x_119_);
lean_dec(v_val_117_);
lean_dec(v_binderName_109_);
return v___x_115_;
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_val_117_);
lean_dec_ref(v___x_115_);
lean_dec(v_binderName_109_);
v___x_146_ = ((lean_object*)(l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1));
v___x_147_ = l_Lean_Core_mkFreshUserName(v___x_146_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_158_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_158_ == 0)
{
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_158_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_158_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v_a_148_);
v___x_153_ = v___x_119_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_157_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_155_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_153_);
v___x_155_ = v___x_150_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_del_object(v___x_119_);
v_a_159_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_147_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_147_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
lean_dec(v_a_116_);
lean_dec(v_binderName_109_);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v___x_115_, 0);
lean_dec(v_unused_176_);
v___x_169_ = v___x_115_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_dec(v___x_115_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_box(0);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___boxed(lean_object* v_binderName_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(lean_object* v_binderName_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_binderName_184_, v_a_185_, v_a_187_, v_a_190_, v_a_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___boxed(lean_object* v_binderName_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(v_binderName_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_203_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(lean_object* v_a_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; uint8_t v___x_209_; 
v_head_207_ = lean_ctor_get(v_x_205_, 0);
v_tail_208_ = lean_ctor_get(v_x_205_, 1);
v___x_209_ = lean_expr_eqv(v_a_204_, v_head_207_);
if (v___x_209_ == 0)
{
v_x_205_ = v_tail_208_;
goto _start;
}
else
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0___boxed(lean_object* v_a_211_, lean_object* v_x_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v_a_211_, v_x_212_);
lean_dec(v_x_212_);
lean_dec_ref(v_a_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(lean_object* v_fvars_215_, lean_object* v_e_216_){
_start:
{
uint8_t v___x_217_; lean_object* v_d_219_; lean_object* v_b_220_; 
v___x_217_ = l_Lean_Expr_hasFVar(v_e_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v_e_216_);
return v___x_217_;
}
else
{
switch(lean_obj_tag(v_e_216_))
{
case 7:
{
lean_object* v_binderType_223_; lean_object* v_body_224_; 
v_binderType_223_ = lean_ctor_get(v_e_216_, 1);
lean_inc_ref(v_binderType_223_);
v_body_224_ = lean_ctor_get(v_e_216_, 2);
lean_inc_ref(v_body_224_);
lean_dec_ref_known(v_e_216_, 3);
v_d_219_ = v_binderType_223_;
v_b_220_ = v_body_224_;
goto v___jp_218_;
}
case 6:
{
lean_object* v_binderType_225_; lean_object* v_body_226_; 
v_binderType_225_ = lean_ctor_get(v_e_216_, 1);
lean_inc_ref(v_binderType_225_);
v_body_226_ = lean_ctor_get(v_e_216_, 2);
lean_inc_ref(v_body_226_);
lean_dec_ref_known(v_e_216_, 3);
v_d_219_ = v_binderType_225_;
v_b_220_ = v_body_226_;
goto v___jp_218_;
}
case 10:
{
lean_object* v_expr_227_; 
v_expr_227_ = lean_ctor_get(v_e_216_, 1);
lean_inc_ref(v_expr_227_);
lean_dec_ref_known(v_e_216_, 2);
v_e_216_ = v_expr_227_;
goto _start;
}
case 8:
{
lean_object* v_type_229_; lean_object* v_value_230_; lean_object* v_body_231_; uint8_t v___x_232_; 
v_type_229_ = lean_ctor_get(v_e_216_, 1);
lean_inc_ref(v_type_229_);
v_value_230_ = lean_ctor_get(v_e_216_, 2);
lean_inc_ref(v_value_230_);
v_body_231_ = lean_ctor_get(v_e_216_, 3);
lean_inc_ref(v_body_231_);
lean_dec_ref_known(v_e_216_, 4);
v___x_232_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_215_, v_type_229_);
if (v___x_232_ == 0)
{
uint8_t v___x_233_; 
v___x_233_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_215_, v_value_230_);
if (v___x_233_ == 0)
{
v_e_216_ = v_body_231_;
goto _start;
}
else
{
lean_dec_ref(v_body_231_);
return v___x_217_;
}
}
else
{
lean_dec_ref(v_body_231_);
lean_dec_ref(v_value_230_);
return v___x_217_;
}
}
case 5:
{
lean_object* v_fn_235_; lean_object* v_arg_236_; uint8_t v___x_237_; 
v_fn_235_ = lean_ctor_get(v_e_216_, 0);
lean_inc_ref(v_fn_235_);
v_arg_236_ = lean_ctor_get(v_e_216_, 1);
lean_inc_ref(v_arg_236_);
lean_dec_ref_known(v_e_216_, 2);
v___x_237_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_215_, v_fn_235_);
if (v___x_237_ == 0)
{
v_e_216_ = v_arg_236_;
goto _start;
}
else
{
lean_dec_ref(v_arg_236_);
return v___x_217_;
}
}
case 11:
{
lean_object* v_struct_239_; 
v_struct_239_ = lean_ctor_get(v_e_216_, 2);
lean_inc_ref(v_struct_239_);
lean_dec_ref_known(v_e_216_, 3);
v_e_216_ = v_struct_239_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_fvarId_241_ = lean_ctor_get(v_e_216_, 0);
lean_inc(v_fvarId_241_);
lean_dec_ref_known(v_e_216_, 1);
v___x_242_ = l_Lean_Expr_fvar___override(v_fvarId_241_);
v___x_243_ = l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v___x_242_, v_fvars_215_);
lean_dec_ref(v___x_242_);
return v___x_243_;
}
default: 
{
uint8_t v___x_244_; 
lean_dec_ref(v_e_216_);
v___x_244_ = 0;
return v___x_244_;
}
}
}
v___jp_218_:
{
uint8_t v___x_221_; 
v___x_221_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_215_, v_d_219_);
if (v___x_221_ == 0)
{
v_e_216_ = v_b_220_;
goto _start;
}
else
{
lean_dec_ref(v_b_220_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1___boxed(lean_object* v_fvars_245_, lean_object* v_e_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_245_, v_e_246_);
lean_dec(v_fvars_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_extractable(lean_object* v_fvars_249_, lean_object* v_e_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_249_, v_e_250_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
v___x_252_ = 1;
return v___x_252_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractable___boxed(lean_object* v_fvars_254_, lean_object* v_e_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_254_, v_e_255_);
lean_dec(v_fvars_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg(lean_object* v_fvars_258_, lean_object* v_n_259_, lean_object* v_t_260_, lean_object* v_v_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___y_268_; lean_object* v___x_273_; lean_object* v_a_274_; uint8_t v___x_275_; 
v___x_273_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_262_, v_a_263_);
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref(v___x_273_);
v___x_275_ = lean_unbox(v_a_274_);
lean_dec(v_a_274_);
if (v___x_275_ == 0)
{
lean_dec_ref(v_v_261_);
lean_dec_ref(v_t_260_);
v___y_268_ = v_a_262_;
goto v___jp_267_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_258_, v_t_260_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_v_261_);
v___y_268_ = v_a_262_;
goto v___jp_267_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_258_, v_v_261_);
if (v___x_277_ == 0)
{
v___y_268_ = v_a_262_;
goto v___jp_267_;
}
else
{
lean_object* v___x_278_; 
lean_inc(v_n_259_);
v___x_278_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(v_n_259_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_289_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
if (lean_obj_tag(v_a_279_) == 1)
{
lean_object* v_val_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_dec(v_n_259_);
v_val_283_ = lean_ctor_get(v_a_279_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v_a_279_, 1);
v___x_284_ = lean_box(v___x_276_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v_val_283_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_285_);
v___x_287_ = v___x_281_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
lean_del_object(v___x_281_);
lean_dec(v_a_279_);
v___y_268_ = v_a_262_;
goto v___jp_267_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec(v_n_259_);
v_a_290_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_278_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_278_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
v___jp_267_:
{
uint8_t v_lift_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_lift_269_ = lean_ctor_get_uint8(v___y_268_, 10);
v___x_270_ = lean_box(v_lift_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_n_259_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___redArg___boxed(lean_object* v_fvars_298_, lean_object* v_n_299_, lean_object* v_t_300_, lean_object* v_v_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_298_, v_n_299_, v_t_300_, v_v_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_fvars_298_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet(lean_object* v_fvars_308_, lean_object* v_n_309_, lean_object* v_t_310_, lean_object* v_v_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_308_, v_n_309_, v_t_310_, v_v_311_, v_a_312_, v_a_314_, v_a_317_, v_a_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_isExtractableLet___boxed(lean_object* v_fvars_321_, lean_object* v_n_322_, lean_object* v_t_323_, lean_object* v_v_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Meta_ExtractLets_isExtractableLet(v_fvars_321_, v_n_322_, v_t_323_, v_v_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_fvars_321_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(lean_object* v_m_334_, lean_object* v_query_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_zero_339_; uint8_t v_isZero_340_; 
v_zero_339_ = lean_unsigned_to_nat(0u);
v_isZero_340_ = lean_nat_dec_eq(v_x_337_, v_zero_339_);
if (v_isZero_340_ == 1)
{
lean_dec(v_x_338_);
lean_dec(v_x_337_);
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_box(2);
return v___x_341_;
}
else
{
lean_object* v_val_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
v_val_342_ = lean_ctor_get(v_x_336_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v_x_336_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_val_342_);
lean_dec(v_x_336_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_val_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_keyArray_350_; lean_object* v_valueArray_351_; lean_object* v___x_352_; uint8_t v_isSome_353_; 
v_keyArray_350_ = lean_ctor_get(v_m_334_, 1);
v_valueArray_351_ = lean_ctor_get(v_m_334_, 2);
v___x_352_ = lean_array_fget_borrowed(v_keyArray_350_, v_x_338_);
v_isSome_353_ = lean_noption_is_some(v___x_352_);
if (v_isSome_353_ == 0)
{
lean_dec(v_x_337_);
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v_x_338_);
return v___x_354_;
}
else
{
lean_object* v_val_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_x_338_);
v_val_355_ = lean_ctor_get(v_x_336_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v_x_336_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_val_355_);
lean_dec(v_x_336_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_val_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_one_363_; lean_object* v_n_364_; lean_object* v___y_366_; 
v_one_363_ = lean_unsigned_to_nat(1u);
v_n_364_ = lean_nat_sub(v_x_337_, v_one_363_);
lean_dec(v_x_337_);
if (v_isSome_353_ == 0)
{
goto v___jp_372_;
}
else
{
lean_object* v___x_374_; uint8_t v_isSome_375_; 
v___x_374_ = lean_array_fget_borrowed(v_valueArray_351_, v_x_338_);
v_isSome_375_ = lean_noption_is_some(v___x_374_);
if (v_isSome_375_ == 0)
{
goto v___jp_372_;
}
else
{
lean_object* v_val_376_; uint8_t v___x_377_; 
lean_inc(v___x_352_);
v_val_376_ = lean_noption_get(v___x_352_);
v___x_377_ = l_Lean_ExprStructEq_beq(v_val_376_, v_query_335_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
lean_dec(v_val_376_);
v___x_378_ = lean_array_get_size(v_keyArray_350_);
v___x_379_ = lean_nat_add(v_x_338_, v_one_363_);
lean_dec(v_x_338_);
v___x_380_ = lean_nat_dec_lt(v___x_379_, v___x_378_);
if (v___x_380_ == 0)
{
lean_dec(v___x_379_);
v_x_337_ = v_n_364_;
v_x_338_ = v_zero_339_;
goto _start;
}
else
{
v_x_337_ = v_n_364_;
v_x_338_ = v___x_379_;
goto _start;
}
}
else
{
lean_object* v_val_383_; lean_object* v___x_384_; 
lean_dec(v_n_364_);
lean_dec(v_x_336_);
lean_inc(v___x_374_);
v_val_383_ = lean_noption_get(v___x_374_);
v___x_384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_384_, 0, v_x_338_);
lean_ctor_set(v___x_384_, 1, v_val_376_);
lean_ctor_set(v___x_384_, 2, v_val_383_);
return v___x_384_;
}
}
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_array_get_size(v_keyArray_350_);
v___x_368_ = lean_nat_add(v_x_338_, v_one_363_);
lean_dec(v_x_338_);
v___x_369_ = lean_nat_dec_lt(v___x_368_, v___x_367_);
if (v___x_369_ == 0)
{
lean_dec(v___x_368_);
v_x_336_ = v___y_366_;
v_x_337_ = v_n_364_;
v_x_338_ = v_zero_339_;
goto _start;
}
else
{
v_x_336_ = v___y_366_;
v_x_337_ = v_n_364_;
v_x_338_ = v___x_368_;
goto _start;
}
}
v___jp_372_:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_373_; 
lean_inc(v_x_338_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_x_338_);
v___y_366_ = v___x_373_;
goto v___jp_365_;
}
else
{
v___y_366_ = v_x_336_;
goto v___jp_365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg___boxed(lean_object* v_m_385_, lean_object* v_query_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_m_385_, v_query_386_, v_x_387_, v_x_388_, v_x_389_);
lean_dec_ref(v_query_386_);
lean_dec_ref(v_m_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(lean_object* v_m_391_, lean_object* v_query_392_){
_start:
{
lean_object* v_keyArray_393_; lean_object* v___x_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v_fold_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_keyArray_393_ = lean_ctor_get(v_m_391_, 1);
v___x_394_ = lean_array_get_size(v_keyArray_393_);
v___x_395_ = l_Lean_ExprStructEq_hash(v_query_392_);
v___x_396_ = 32ULL;
v___x_397_ = lean_uint64_shift_right(v___x_395_, v___x_396_);
v_fold_398_ = lean_uint64_xor(v___x_395_, v___x_397_);
v___x_399_ = 16ULL;
v___x_400_ = lean_uint64_shift_right(v_fold_398_, v___x_399_);
v___x_401_ = lean_uint64_xor(v_fold_398_, v___x_400_);
v___x_402_ = lean_uint64_to_usize(v___x_401_);
v___x_403_ = lean_usize_of_nat(v___x_394_);
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_sub(v___x_403_, v___x_404_);
v___x_406_ = lean_usize_land(v___x_402_, v___x_405_);
v___x_407_ = lean_usize_to_nat(v___x_406_);
v___x_408_ = lean_box(0);
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_m_391_, v_query_392_, v___x_408_, v___x_394_, v___x_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg___boxed(lean_object* v_m_410_, lean_object* v_query_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_m_410_, v_query_411_);
lean_dec_ref(v_query_411_);
lean_dec_ref(v_m_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___redArg(lean_object* v_b_413_, lean_object* v_acc_414_, lean_object* v_i_415_){
_start:
{
lean_object* v___y_417_; lean_object* v_keyArray_425_; lean_object* v_valueArray_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_keyArray_425_ = lean_ctor_get(v_b_413_, 1);
v_valueArray_426_ = lean_ctor_get(v_b_413_, 2);
v___x_427_ = lean_array_get_size(v_keyArray_425_);
v___x_428_ = lean_nat_dec_lt(v_i_415_, v___x_427_);
if (v___x_428_ == 0)
{
lean_dec(v_i_415_);
return v_acc_414_;
}
else
{
lean_object* v___x_429_; uint8_t v_isSome_430_; 
v___x_429_ = lean_array_fget_borrowed(v_keyArray_425_, v_i_415_);
v_isSome_430_ = lean_noption_is_some(v___x_429_);
if (v_isSome_430_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_431_; uint8_t v_isSome_432_; 
v___x_431_ = lean_array_fget_borrowed(v_valueArray_426_, v_i_415_);
v_isSome_432_ = lean_noption_is_some(v___x_431_);
if (v_isSome_432_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v_val_433_; lean_object* v_val_434_; lean_object* v_i_436_; lean_object* v___x_441_; 
lean_inc(v___x_429_);
v_val_433_ = lean_noption_get(v___x_429_);
lean_inc(v___x_431_);
v_val_434_ = lean_noption_get(v___x_431_);
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_acc_414_, v_val_433_);
switch(lean_obj_tag(v___x_441_))
{
case 0:
{
lean_object* v_index_442_; lean_object* v_size_443_; lean_object* v___x_444_; 
v_index_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_index_442_);
lean_dec_ref_known(v___x_441_, 3);
v_size_443_ = lean_ctor_get(v_acc_414_, 0);
lean_inc(v_size_443_);
v___x_444_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_414_, v_size_443_, v_index_442_, v_val_433_, v_val_434_);
lean_dec(v_index_442_);
v___y_417_ = v___x_444_;
goto v___jp_416_;
}
case 1:
{
lean_object* v_index_445_; 
v_index_445_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_index_445_);
lean_dec_ref_known(v___x_441_, 1);
v_i_436_ = v_index_445_;
goto v___jp_435_;
}
default: 
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_414_, v___x_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_index_448_; 
v_index_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_index_448_);
lean_dec_ref_known(v___x_447_, 1);
v_i_436_ = v_index_448_;
goto v___jp_435_;
}
else
{
lean_dec(v_val_434_);
lean_dec(v_val_433_);
v___y_417_ = v_acc_414_;
goto v___jp_416_;
}
}
}
v___jp_435_:
{
lean_object* v_size_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_size_437_ = lean_ctor_get(v_acc_414_, 0);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_size_437_, v___x_438_);
v___x_440_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_414_, v___x_439_, v_i_436_, v_val_433_, v_val_434_);
lean_dec(v_i_436_);
v___y_417_ = v___x_440_;
goto v___jp_416_;
}
}
}
}
v___jp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_i_415_, v___x_418_);
lean_dec(v_i_415_);
v_acc_414_ = v___y_417_;
v_i_415_ = v___x_419_;
goto _start;
}
v___jp_421_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_i_415_, v___x_422_);
lean_dec(v_i_415_);
v_i_415_ = v___x_423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_449_, lean_object* v_acc_450_, lean_object* v_i_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___redArg(v_b_449_, v_acc_450_, v_i_451_);
lean_dec_ref(v_b_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___redArg(lean_object* v_init_453_, lean_object* v_b_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___redArg(v_b_454_, v_init_453_, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___redArg___boxed(lean_object* v_init_457_, lean_object* v_b_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___redArg(v_init_457_, v_b_458_);
lean_dec_ref(v_b_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(lean_object* v_m_460_){
_start:
{
lean_object* v_keyArray_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_cellCount_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_target_468_; lean_object* v___x_469_; 
v_keyArray_461_ = lean_ctor_get(v_m_460_, 1);
v___x_462_ = lean_array_get_size(v_keyArray_461_);
v___x_463_ = lean_unsigned_to_nat(2u);
v_cellCount_464_ = lean_nat_mul(v___x_462_, v___x_463_);
v___x_465_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_464_);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_464_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_464_);
v_target_468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_468_, 0, v___x_465_);
lean_ctor_set(v_target_468_, 1, v___x_466_);
lean_ctor_set(v_target_468_, 2, v___x_467_);
v___x_469_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___redArg(v_target_468_, v_m_460_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg___boxed(lean_object* v_m_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_m_470_);
lean_dec_ref(v_m_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg(lean_object* v_decl_472_, uint8_t v_isLet_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_fst_479_; lean_object* v_snd_480_; lean_object* v_givenNames_483_; lean_object* v_decls_484_; lean_object* v_valueMap_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_566_; 
v___x_477_ = lean_st_ref_take(v_a_475_);
v_givenNames_483_ = lean_ctor_get(v___x_477_, 0);
v_decls_484_ = lean_ctor_get(v___x_477_, 1);
v_valueMap_485_ = lean_ctor_get(v___x_477_, 2);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_566_ == 0)
{
v___x_487_ = v___x_477_;
v_isShared_488_ = v_isSharedCheck_566_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_valueMap_485_);
lean_inc(v_decls_484_);
lean_inc(v_givenNames_483_);
lean_dec(v___x_477_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_566_;
goto v_resetjp_486_;
}
v___jp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_st_ref_put(v_a_475_, v_snd_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_fst_479_);
return v___x_482_;
}
v_resetjp_486_:
{
uint8_t v_merge_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___y_494_; 
v_merge_489_ = lean_ctor_get_uint8(v_a_474_, 6);
v___x_490_ = lean_box(0);
lean_inc_ref(v_decl_472_);
v___x_491_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_491_, 0, v_decl_472_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*1, v_isLet_473_);
v___x_492_ = lean_array_push(v_decls_484_, v___x_491_);
if (v_merge_489_ == 0)
{
lean_object* v___x_498_; 
lean_del_object(v___x_487_);
lean_dec_ref(v_decl_472_);
v___x_498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_498_, 0, v_givenNames_483_);
lean_ctor_set(v___x_498_, 1, v___x_492_);
lean_ctor_set(v___x_498_, 2, v_valueMap_485_);
v_fst_479_ = v___x_490_;
v_snd_480_ = v___x_498_;
goto v___jp_478_;
}
else
{
uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___y_503_; lean_object* v_i_504_; lean_object* v___y_510_; lean_object* v___y_520_; lean_object* v_i_521_; lean_object* v___x_536_; 
v___x_499_ = 0;
v___x_500_ = l_Lean_LocalDecl_value(v_decl_472_, v___x_499_);
v___x_501_ = l_Lean_LocalDecl_fvarId(v_decl_472_);
lean_dec_ref(v_decl_472_);
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_485_, v___x_500_);
switch(lean_obj_tag(v___x_536_))
{
case 0:
{
lean_object* v_index_537_; lean_object* v_size_538_; lean_object* v___x_539_; 
v_index_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_index_537_);
lean_dec_ref_known(v___x_536_, 3);
v_size_538_ = lean_ctor_get(v_valueMap_485_, 0);
lean_inc(v_size_538_);
v___x_539_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_485_, v_size_538_, v_index_537_, v___x_500_, v___x_501_);
lean_dec(v_index_537_);
v___y_494_ = v___x_539_;
goto v___jp_493_;
}
case 1:
{
lean_object* v_index_540_; lean_object* v_size_541_; lean_object* v_keyArray_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_index_540_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_index_540_);
lean_dec_ref_known(v___x_536_, 1);
v_size_541_ = lean_ctor_get(v_valueMap_485_, 0);
v_keyArray_542_ = lean_ctor_get(v_valueMap_485_, 1);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_size_541_, v___x_543_);
v___x_545_ = lean_array_get_size(v_keyArray_542_);
v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v___x_544_);
lean_dec(v_index_540_);
goto v___jp_526_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_547_ = lean_unsigned_to_nat(4u);
v___x_548_ = lean_nat_mul(v___x_544_, v___x_547_);
v___x_549_ = lean_unsigned_to_nat(3u);
v___x_550_ = lean_nat_mul(v___x_545_, v___x_549_);
v___x_551_ = lean_nat_dec_le(v___x_548_, v___x_550_);
lean_dec(v___x_550_);
lean_dec(v___x_548_);
if (v___x_551_ == 0)
{
lean_dec(v___x_544_);
lean_dec(v_index_540_);
goto v___jp_526_;
}
else
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_485_, v___x_544_, v_index_540_, v___x_500_, v___x_501_);
lean_dec(v_index_540_);
v___y_494_ = v___x_552_;
goto v___jp_493_;
}
}
}
default: 
{
lean_object* v_size_553_; lean_object* v_keyArray_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_size_553_ = lean_ctor_get(v_valueMap_485_, 0);
v_keyArray_554_ = lean_ctor_get(v_valueMap_485_, 1);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_size_553_, v___x_555_);
v___x_557_ = lean_array_get_size(v_keyArray_554_);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v___x_556_);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_valueMap_485_);
lean_dec_ref(v_valueMap_485_);
v___y_510_ = v___x_559_;
goto v___jp_509_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_560_ = lean_unsigned_to_nat(4u);
v___x_561_ = lean_nat_mul(v___x_556_, v___x_560_);
lean_dec(v___x_556_);
v___x_562_ = lean_unsigned_to_nat(3u);
v___x_563_ = lean_nat_mul(v___x_557_, v___x_562_);
v___x_564_ = lean_nat_dec_le(v___x_561_, v___x_563_);
lean_dec(v___x_563_);
lean_dec(v___x_561_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_valueMap_485_);
lean_dec_ref(v_valueMap_485_);
v___y_510_ = v___x_565_;
goto v___jp_509_;
}
else
{
v___y_510_ = v_valueMap_485_;
goto v___jp_509_;
}
}
}
}
v___jp_502_:
{
lean_object* v_size_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_size_505_ = lean_ctor_get(v___y_503_, 0);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_size_505_, v___x_506_);
v___x_508_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_503_, v___x_507_, v_i_504_, v___x_500_, v___x_501_);
lean_dec(v_i_504_);
v___y_494_ = v___x_508_;
goto v___jp_493_;
}
v___jp_509_:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v___y_510_, v___x_500_);
switch(lean_obj_tag(v___x_511_))
{
case 0:
{
lean_object* v_index_512_; lean_object* v_size_513_; lean_object* v___x_514_; 
v_index_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_index_512_);
lean_dec_ref_known(v___x_511_, 3);
v_size_513_ = lean_ctor_get(v___y_510_, 0);
lean_inc(v_size_513_);
v___x_514_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_510_, v_size_513_, v_index_512_, v___x_500_, v___x_501_);
lean_dec(v_index_512_);
v___y_494_ = v___x_514_;
goto v___jp_493_;
}
case 1:
{
lean_object* v_index_515_; 
v_index_515_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_index_515_);
lean_dec_ref_known(v___x_511_, 1);
v___y_503_ = v___y_510_;
v_i_504_ = v_index_515_;
goto v___jp_502_;
}
default: 
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_510_, v___x_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_index_518_; 
v_index_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_index_518_);
lean_dec_ref_known(v___x_517_, 1);
v___y_503_ = v___y_510_;
v_i_504_ = v_index_518_;
goto v___jp_502_;
}
else
{
lean_dec(v___x_501_);
lean_dec_ref(v___x_500_);
v___y_494_ = v___y_510_;
goto v___jp_493_;
}
}
}
}
v___jp_519_:
{
lean_object* v_size_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_size_522_ = lean_ctor_get(v___y_520_, 0);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_size_522_, v___x_523_);
v___x_525_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_520_, v___x_524_, v_i_521_, v___x_500_, v___x_501_);
lean_dec(v_i_521_);
v___y_494_ = v___x_525_;
goto v___jp_493_;
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_valueMap_485_);
lean_dec_ref(v_valueMap_485_);
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v___x_527_, v___x_500_);
switch(lean_obj_tag(v___x_528_))
{
case 0:
{
lean_object* v_index_529_; lean_object* v_size_530_; lean_object* v___x_531_; 
v_index_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_index_529_);
lean_dec_ref_known(v___x_528_, 3);
v_size_530_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_size_530_);
v___x_531_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_527_, v_size_530_, v_index_529_, v___x_500_, v___x_501_);
lean_dec(v_index_529_);
v___y_494_ = v___x_531_;
goto v___jp_493_;
}
case 1:
{
lean_object* v_index_532_; 
v_index_532_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_index_532_);
lean_dec_ref_known(v___x_528_, 1);
v___y_520_ = v___x_527_;
v_i_521_ = v_index_532_;
goto v___jp_519_;
}
default: 
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_527_, v___x_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_index_535_; 
v_index_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_index_535_);
lean_dec_ref_known(v___x_534_, 1);
v___y_520_ = v___x_527_;
v_i_521_ = v_index_535_;
goto v___jp_519_;
}
else
{
lean_dec(v___x_501_);
lean_dec_ref(v___x_500_);
v___y_494_ = v___x_527_;
goto v___jp_493_;
}
}
}
}
}
v___jp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 2, v___y_494_);
lean_ctor_set(v___x_487_, 1, v___x_492_);
v___x_496_ = v___x_487_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_givenNames_483_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v___y_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
v_fst_479_ = v___x_490_;
v_snd_480_ = v___x_496_;
goto v___jp_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___redArg___boxed(lean_object* v_decl_567_, lean_object* v_isLet_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
uint8_t v_isLet_boxed_572_; lean_object* v_res_573_; 
v_isLet_boxed_572_ = lean_unbox(v_isLet_568_);
v_res_573_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_567_, v_isLet_boxed_572_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl(lean_object* v_decl_574_, uint8_t v_isLet_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_574_, v_isLet_575_, v_a_576_, v_a_578_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_addDecl___boxed(lean_object* v_decl_585_, lean_object* v_isLet_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
uint8_t v_isLet_boxed_595_; lean_object* v_res_596_; 
v_isLet_boxed_595_ = lean_unbox(v_isLet_586_);
v_res_596_ = l_Lean_Meta_ExtractLets_addDecl(v_decl_585_, v_isLet_boxed_595_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0(lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_query_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_m_598_, v_query_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___boxed(lean_object* v_00_u03b2_601_, lean_object* v_m_602_, lean_object* v_query_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0(v_00_u03b2_601_, v_m_602_, v_query_603_);
lean_dec_ref(v_query_603_);
lean_dec_ref(v_m_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1(lean_object* v_00_u03b2_605_, lean_object* v_m_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_m_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___boxed(lean_object* v_00_u03b2_608_, lean_object* v_m_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1(v_00_u03b2_608_, v_m_609_);
lean_dec_ref(v_m_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(lean_object* v_00_u03b2_611_, lean_object* v_m_612_, lean_object* v_query_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_m_612_, v_query_613_, v_x_614_, v_x_615_, v_x_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_619_, lean_object* v_m_620_, lean_object* v_query_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(v_00_u03b2_619_, v_m_620_, v_query_621_, v_x_622_, v_x_623_, v_x_624_, v_x_625_);
lean_dec_ref(v_query_621_);
lean_dec_ref(v_m_620_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2(lean_object* v_00_u03b2_627_, lean_object* v_init_628_, lean_object* v_b_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___redArg(v_init_628_, v_b_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_631_, lean_object* v_init_632_, lean_object* v_b_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2(v_00_u03b2_631_, v_init_632_, v_b_633_);
lean_dec_ref(v_b_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_635_, lean_object* v_b_636_, lean_object* v_acc_637_, lean_object* v_i_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___redArg(v_b_636_, v_acc_637_, v_i_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_640_, lean_object* v_b_641_, lean_object* v_acc_642_, lean_object* v_i_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1_spec__2_spec__3(v_00_u03b2_640_, v_b_641_, v_acc_642_, v_i_643_);
lean_dec_ref(v_b_641_);
return v_res_644_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(lean_object* v_k_645_, lean_object* v_t_646_){
_start:
{
if (lean_obj_tag(v_t_646_) == 0)
{
lean_object* v_k_647_; lean_object* v_l_648_; lean_object* v_r_649_; uint8_t v___x_650_; 
v_k_647_ = lean_ctor_get(v_t_646_, 1);
v_l_648_ = lean_ctor_get(v_t_646_, 3);
v_r_649_ = lean_ctor_get(v_t_646_, 4);
v___x_650_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_645_, v_k_647_);
switch(v___x_650_)
{
case 0:
{
v_t_646_ = v_l_648_;
goto _start;
}
case 1:
{
uint8_t v___x_652_; 
v___x_652_ = 1;
return v___x_652_;
}
default: 
{
v_t_646_ = v_r_649_;
goto _start;
}
}
}
else
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg___boxed(lean_object* v_k_655_, lean_object* v_t_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_655_, v_t_656_);
lean_dec(v_t_656_);
lean_dec(v_k_655_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(lean_object* v___x_659_, lean_object* v_e_660_){
_start:
{
uint8_t v___x_661_; lean_object* v_d_663_; lean_object* v_b_664_; 
v___x_661_ = l_Lean_Expr_hasFVar(v_e_660_);
if (v___x_661_ == 0)
{
return v___x_661_;
}
else
{
switch(lean_obj_tag(v_e_660_))
{
case 7:
{
lean_object* v_binderType_667_; lean_object* v_body_668_; 
v_binderType_667_ = lean_ctor_get(v_e_660_, 1);
v_body_668_ = lean_ctor_get(v_e_660_, 2);
v_d_663_ = v_binderType_667_;
v_b_664_ = v_body_668_;
goto v___jp_662_;
}
case 6:
{
lean_object* v_binderType_669_; lean_object* v_body_670_; 
v_binderType_669_ = lean_ctor_get(v_e_660_, 1);
v_body_670_ = lean_ctor_get(v_e_660_, 2);
v_d_663_ = v_binderType_669_;
v_b_664_ = v_body_670_;
goto v___jp_662_;
}
case 10:
{
lean_object* v_expr_671_; 
v_expr_671_ = lean_ctor_get(v_e_660_, 1);
v_e_660_ = v_expr_671_;
goto _start;
}
case 8:
{
lean_object* v_type_673_; lean_object* v_value_674_; lean_object* v_body_675_; uint8_t v___x_676_; 
v_type_673_ = lean_ctor_get(v_e_660_, 1);
v_value_674_ = lean_ctor_get(v_e_660_, 2);
v_body_675_ = lean_ctor_get(v_e_660_, 3);
v___x_676_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_659_, v_type_673_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; 
v___x_677_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_659_, v_value_674_);
if (v___x_677_ == 0)
{
v_e_660_ = v_body_675_;
goto _start;
}
else
{
return v___x_661_;
}
}
else
{
return v___x_661_;
}
}
case 5:
{
lean_object* v_fn_679_; lean_object* v_arg_680_; uint8_t v___x_681_; 
v_fn_679_ = lean_ctor_get(v_e_660_, 0);
v_arg_680_ = lean_ctor_get(v_e_660_, 1);
v___x_681_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_659_, v_fn_679_);
if (v___x_681_ == 0)
{
v_e_660_ = v_arg_680_;
goto _start;
}
else
{
return v___x_661_;
}
}
case 11:
{
lean_object* v_struct_683_; 
v_struct_683_ = lean_ctor_get(v_e_660_, 2);
v_e_660_ = v_struct_683_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_685_; uint8_t v___x_686_; 
v_fvarId_685_ = lean_ctor_get(v_e_660_, 0);
v___x_686_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_fvarId_685_, v___x_659_);
return v___x_686_;
}
default: 
{
uint8_t v___x_687_; 
v___x_687_ = 0;
return v___x_687_;
}
}
}
v___jp_662_:
{
uint8_t v___x_665_; 
v___x_665_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_659_, v_d_663_);
if (v___x_665_ == 0)
{
v_e_660_ = v_b_664_;
goto _start;
}
else
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1___boxed(lean_object* v___x_688_, lean_object* v_e_689_){
_start:
{
uint8_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_688_, v_e_689_);
lean_dec_ref(v_e_689_);
lean_dec(v___x_688_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(lean_object* v_as_692_, size_t v_sz_693_, size_t v_i_694_, lean_object* v_b_695_){
_start:
{
lean_object* v_a_698_; uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_694_, v_sz_693_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_b_695_);
return v___x_703_;
}
else
{
lean_object* v_snd_704_; lean_object* v_fst_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_739_; 
v_snd_704_ = lean_ctor_get(v_b_695_, 1);
v_fst_705_ = lean_ctor_get(v_b_695_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_b_695_);
if (v_isSharedCheck_739_ == 0)
{
v___x_707_ = v_b_695_;
v_isShared_708_ = v_isSharedCheck_739_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snd_704_);
lean_inc(v_fst_705_);
lean_dec(v_b_695_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_739_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_738_; 
v_fst_709_ = lean_ctor_get(v_snd_704_, 0);
v_snd_710_ = lean_ctor_get(v_snd_704_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_snd_704_);
if (v_isSharedCheck_738_ == 0)
{
v___x_712_ = v_snd_704_;
v_isShared_713_ = v_isSharedCheck_738_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_snd_704_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_738_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_a_714_; lean_object* v_decl_715_; uint8_t v___y_717_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_a_714_ = lean_array_uget_borrowed(v_as_692_, v_i_694_);
v_decl_715_ = lean_ctor_get(v_a_714_, 0);
v___x_734_ = l_Lean_LocalDecl_type(v_decl_715_);
v___x_735_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_705_, v___x_734_);
lean_dec_ref(v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = l_Lean_LocalDecl_value(v_decl_715_, v___x_735_);
v___x_737_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_705_, v___x_736_);
lean_dec_ref(v___x_736_);
v___y_717_ = v___x_737_;
goto v___jp_716_;
}
else
{
v___y_717_ = v___x_735_;
goto v___jp_716_;
}
v___jp_716_:
{
if (v___y_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_720_; 
lean_inc(v_a_714_);
v___x_718_ = lean_array_push(v_fst_709_, v_a_714_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_718_);
v___x_720_ = v___x_712_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_snd_710_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_720_);
v___x_722_ = v___x_707_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fst_705_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v_a_698_ = v___x_722_;
goto v___jp_697_;
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
lean_inc(v_a_714_);
v___x_725_ = lean_array_push(v_snd_710_, v_a_714_);
v___x_726_ = l_Lean_LocalDecl_fvarId(v_decl_715_);
v___x_727_ = l_Lean_FVarIdSet_insert(v_fst_705_, v___x_726_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___x_725_);
v___x_729_ = v___x_712_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_725_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_729_);
lean_ctor_set(v___x_707_, 0, v___x_727_);
v___x_731_ = v___x_707_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v_a_698_ = v___x_731_;
goto v___jp_697_;
}
}
}
}
}
}
}
v___jp_697_:
{
size_t v___x_699_; size_t v___x_700_; 
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_i_694_, v___x_699_);
v_i_694_ = v___x_700_;
v_b_695_ = v_a_698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(lean_object* v_as_740_, lean_object* v_sz_741_, lean_object* v_i_742_, lean_object* v_b_743_, lean_object* v___y_744_){
_start:
{
size_t v_sz_boxed_745_; size_t v_i_boxed_746_; lean_object* v_res_747_; 
v_sz_boxed_745_ = lean_unbox_usize(v_sz_741_);
lean_dec(v_sz_741_);
v_i_boxed_746_ = lean_unbox_usize(v_i_742_);
lean_dec(v_i_742_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_740_, v_sz_boxed_745_, v_i_boxed_746_, v_b_743_);
lean_dec_ref(v_as_740_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls(lean_object* v_fvar_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_decls_760_; lean_object* v_fvarSet_761_; lean_object* v_fvarSet_762_; lean_object* v___x_763_; lean_object* v___x_764_; size_t v_sz_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_759_ = lean_st_ref_get(v_a_753_);
v_decls_760_ = lean_ctor_get(v___x_759_, 1);
lean_inc_ref(v_decls_760_);
lean_dec(v___x_759_);
v_fvarSet_761_ = lean_box(1);
v_fvarSet_762_ = l_Lean_FVarIdSet_insert(v_fvarSet_761_, v_fvar_750_);
v___x_763_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_fvarSet_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v_sz_765_ = lean_array_size(v_decls_760_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_decls_760_, v_sz_765_, v___x_766_, v___x_764_);
lean_dec_ref(v_decls_760_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_790_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_790_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v_snd_773_; lean_object* v_fst_774_; lean_object* v_snd_775_; lean_object* v_givenNames_776_; lean_object* v_valueMap_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_788_; 
v___x_772_ = lean_st_ref_take(v_a_753_);
v_snd_773_ = lean_ctor_get(v_a_768_, 1);
lean_inc(v_snd_773_);
lean_dec(v_a_768_);
v_fst_774_ = lean_ctor_get(v_snd_773_, 0);
lean_inc(v_fst_774_);
v_snd_775_ = lean_ctor_get(v_snd_773_, 1);
lean_inc(v_snd_775_);
lean_dec(v_snd_773_);
v_givenNames_776_ = lean_ctor_get(v___x_772_, 0);
v_valueMap_777_ = lean_ctor_get(v___x_772_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_772_, 1);
lean_dec(v_unused_789_);
v___x_779_ = v___x_772_;
v_isShared_780_ = v_isSharedCheck_788_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_valueMap_777_);
lean_inc(v_givenNames_776_);
lean_dec(v___x_772_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_788_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_fst_774_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_givenNames_776_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_fst_774_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_valueMap_777_);
v___x_782_ = v_reuseFailAlloc_787_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_st_ref_put(v_a_753_, v___x_782_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v_snd_775_);
v___x_785_ = v___x_770_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_snd_775_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_767_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_767_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_flushDecls___boxed(lean_object* v_fvar_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_ExtractLets_flushDecls(v_fvar_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(lean_object* v_00_u03b2_809_, lean_object* v_k_810_, lean_object* v_t_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_810_, v_t_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(lean_object* v_00_u03b2_813_, lean_object* v_k_814_, lean_object* v_t_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(v_00_u03b2_813_, v_k_814_, v_t_815_);
lean_dec(v_t_815_);
lean_dec(v_k_814_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(lean_object* v_as_818_, size_t v_sz_819_, size_t v_i_820_, lean_object* v_b_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_818_, v_sz_819_, v_i_820_, v_b_821_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(lean_object* v_as_831_, lean_object* v_sz_832_, lean_object* v_i_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
size_t v_sz_boxed_843_; size_t v_i_boxed_844_; lean_object* v_res_845_; 
v_sz_boxed_843_ = lean_unbox_usize(v_sz_832_);
lean_dec(v_sz_832_);
v_i_boxed_844_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_831_, v_sz_boxed_843_, v_i_boxed_844_, v_b_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v_as_831_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(lean_object* v_x_846_){
_start:
{
lean_object* v_decl_847_; 
v_decl_847_ = lean_ctor_get(v_x_846_, 0);
lean_inc_ref(v_decl_847_);
return v_decl_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(v_x_848_);
lean_dec_ref(v_x_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(lean_object* v_lctx_850_, lean_object* v_x1_851_, lean_object* v_x2_852_){
_start:
{
lean_object* v_decl_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_decl_853_ = lean_ctor_get(v_x2_852_, 0);
v___x_854_ = l_Lean_LocalDecl_fvarId(v_decl_853_);
v___x_855_ = l_Lean_LocalContext_contains(v_lctx_850_, v___x_854_);
lean_dec(v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_array_push(v_x1_851_, v_x2_852_);
return v___x_856_;
}
else
{
lean_dec_ref(v_x2_852_);
return v_x1_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(lean_object* v_lctx_857_, lean_object* v_x1_858_, lean_object* v_x2_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(v_lctx_857_, v_x1_858_, v_x2_859_);
lean_dec_ref(v_lctx_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(lean_object* v___f_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_k_883_, lean_object* v_decls_884_, lean_object* v_lctx_885_){
_start:
{
lean_object* v___y_887_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_array_get_size(v_decls_884_);
v___x_896_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_897_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v___x_898_ = lean_nat_dec_lt(v___x_894_, v___x_895_);
if (v___x_898_ == 0)
{
lean_dec_ref(v_lctx_885_);
lean_dec_ref(v_decls_884_);
v___y_887_ = v___x_896_;
goto v___jp_886_;
}
else
{
lean_object* v___f_899_; uint8_t v___x_900_; 
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_899_, 0, v_lctx_885_);
v___x_900_ = lean_nat_dec_le(v___x_895_, v___x_895_);
if (v___x_900_ == 0)
{
if (v___x_898_ == 0)
{
lean_dec_ref(v___f_899_);
lean_dec_ref(v_decls_884_);
v___y_887_ = v___x_896_;
goto v___jp_886_;
}
else
{
size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_895_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_897_, v___f_899_, v_decls_884_, v___x_901_, v___x_902_, v___x_896_);
v___y_887_ = v___x_903_;
goto v___jp_886_;
}
}
else
{
size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((size_t)0ULL);
v___x_905_ = lean_usize_of_nat(v___x_895_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_897_, v___f_899_, v_decls_884_, v___x_904_, v___x_905_, v___x_896_);
v___y_887_ = v___x_906_;
goto v___jp_886_;
}
}
v___jp_886_:
{
lean_object* v___x_888_; size_t v_sz_889_; size_t v___x_890_; lean_object* v_decls_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_888_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9));
v_sz_889_ = lean_array_size(v___y_887_);
v___x_890_ = ((size_t)0ULL);
v_decls_891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_888_, v___f_880_, v_sz_889_, v___x_890_, v___y_887_);
v___x_892_ = lean_array_to_list(v_decls_891_);
v___x_893_ = l_Lean_Meta_withExistingLocalDecls___redArg(v_inst_881_, v_inst_882_, v___x_892_, v_k_883_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_decls_911_, lean_object* v_k_912_){
_start:
{
lean_object* v_toBind_913_; lean_object* v___f_914_; lean_object* v___f_915_; lean_object* v___x_916_; 
v_toBind_913_ = lean_ctor_get(v_inst_908_, 1);
lean_inc(v_toBind_913_);
v___f_914_ = ((lean_object*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0));
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2), 6, 5);
lean_closure_set(v___f_915_, 0, v___f_914_);
lean_closure_set(v___f_915_, 1, v_inst_909_);
lean_closure_set(v___f_915_, 2, v_inst_908_);
lean_closure_set(v___f_915_, 3, v_k_912_);
lean_closure_set(v___f_915_, 4, v_decls_911_);
v___x_916_ = lean_apply_4(v_toBind_913_, lean_box(0), lean_box(0), v_inst_910_, v___f_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(lean_object* v_m_917_, lean_object* v_00_u03b1_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_decls_922_, lean_object* v_k_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(v_inst_919_, v_inst_920_, v_inst_921_, v_decls_922_, v_k_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(lean_object* v_as_925_, size_t v_i_926_, size_t v_stop_927_, lean_object* v_b_928_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = lean_usize_dec_eq(v_i_926_, v_stop_927_);
if (v___x_929_ == 0)
{
size_t v___x_930_; size_t v___x_931_; lean_object* v___x_932_; lean_object* v_decl_933_; uint8_t v_isLet_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_sub(v_i_926_, v___x_930_);
v___x_932_ = lean_array_uget_borrowed(v_as_925_, v___x_931_);
v_decl_933_ = lean_ctor_get(v___x_932_, 0);
v_isLet_934_ = lean_ctor_get_uint8(v___x_932_, sizeof(void*)*1);
v___x_935_ = l_Lean_LocalDecl_userName(v_decl_933_);
v___x_936_ = l_Lean_LocalDecl_type(v_decl_933_);
v___x_937_ = l_Lean_LocalDecl_value(v_decl_933_, v___x_929_);
lean_inc_ref(v_decl_933_);
v___x_938_ = l_Lean_LocalDecl_toExpr(v_decl_933_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_array_push(v___x_940_, v___x_938_);
v___x_942_ = lean_expr_abstract(v_b_928_, v___x_941_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v_b_928_);
if (v_isLet_934_ == 0)
{
uint8_t v___x_943_; lean_object* v___x_944_; 
v___x_943_ = 1;
v___x_944_ = l_Lean_Expr_letE___override(v___x_935_, v___x_936_, v___x_937_, v___x_942_, v___x_943_);
v_i_926_ = v___x_931_;
v_b_928_ = v___x_944_;
goto _start;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Expr_letE___override(v___x_935_, v___x_936_, v___x_937_, v___x_942_, v___x_929_);
v_i_926_ = v___x_931_;
v_b_928_ = v___x_946_;
goto _start;
}
}
else
{
return v_b_928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(lean_object* v_as_948_, lean_object* v_i_949_, lean_object* v_stop_950_, lean_object* v_b_951_){
_start:
{
size_t v_i_boxed_952_; size_t v_stop_boxed_953_; lean_object* v_res_954_; 
v_i_boxed_952_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_stop_boxed_953_ = lean_unbox_usize(v_stop_950_);
lean_dec(v_stop_950_);
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_948_, v_i_boxed_952_, v_stop_boxed_953_, v_b_951_);
lean_dec_ref(v_as_948_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls(lean_object* v_decls_955_, lean_object* v_e_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = lean_array_get_size(v_decls_955_);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_nat_dec_lt(v___x_958_, v___x_957_);
if (v___x_959_ == 0)
{
return v_e_956_;
}
else
{
size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_usize_of_nat(v___x_957_);
v___x_961_ = ((size_t)0ULL);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_955_, v___x_960_, v___x_961_, v_e_956_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_mkLetDecls___boxed(lean_object* v_decls_963_, lean_object* v_e_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_963_, v_e_964_);
lean_dec_ref(v_decls_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(lean_object* v_fvarId_966_, size_t v_sz_967_, size_t v_i_968_, lean_object* v_bs_969_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = lean_usize_dec_lt(v_i_968_, v_sz_967_);
if (v___x_970_ == 0)
{
return v_bs_969_;
}
else
{
lean_object* v_v_971_; lean_object* v_decl_972_; lean_object* v___x_973_; lean_object* v_bs_x27_974_; lean_object* v___y_976_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_v_971_ = lean_array_uget(v_bs_969_, v_i_968_);
v_decl_972_ = lean_ctor_get(v_v_971_, 0);
v___x_973_ = lean_unsigned_to_nat(0u);
v_bs_x27_974_ = lean_array_uset(v_bs_969_, v_i_968_, v___x_973_);
v___x_981_ = l_Lean_LocalDecl_fvarId(v_decl_972_);
v___x_982_ = l_Lean_instBEqFVarId_beq(v___x_981_, v_fvarId_966_);
lean_dec(v___x_981_);
if (v___x_982_ == 0)
{
v___y_976_ = v_v_971_;
goto v___jp_975_;
}
else
{
lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_inc_ref(v_decl_972_);
v_isSharedCheck_989_ = !lean_is_exclusive(v_v_971_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_v_971_, 0);
lean_dec(v_unused_990_);
v___x_984_ = v_v_971_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_dec(v_v_971_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_decl_972_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*1, v___x_982_);
v___y_976_ = v___x_987_;
goto v___jp_975_;
}
}
}
v___jp_975_:
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_add(v_i_968_, v___x_977_);
v___x_979_ = lean_array_uset(v_bs_x27_974_, v_i_968_, v___y_976_);
v_i_968_ = v___x_978_;
v_bs_969_ = v___x_979_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(lean_object* v_fvarId_991_, lean_object* v_sz_992_, lean_object* v_i_993_, lean_object* v_bs_994_){
_start:
{
size_t v_sz_boxed_995_; size_t v_i_boxed_996_; lean_object* v_res_997_; 
v_sz_boxed_995_ = lean_unbox_usize(v_sz_992_);
lean_dec(v_sz_992_);
v_i_boxed_996_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_991_, v_sz_boxed_995_, v_i_boxed_996_, v_bs_994_);
lean_dec(v_fvarId_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg(lean_object* v_fvarId_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v_givenNames_1002_; lean_object* v_decls_1003_; lean_object* v_valueMap_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1017_; 
v___x_1001_ = lean_st_ref_take(v_a_999_);
v_givenNames_1002_ = lean_ctor_get(v___x_1001_, 0);
v_decls_1003_ = lean_ctor_get(v___x_1001_, 1);
v_valueMap_1004_ = lean_ctor_get(v___x_1001_, 2);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1006_ = v___x_1001_;
v_isShared_1007_ = v_isSharedCheck_1017_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_valueMap_1004_);
lean_inc(v_decls_1003_);
lean_inc(v_givenNames_1002_);
lean_dec(v___x_1001_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1017_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
size_t v_sz_1008_; size_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_sz_1008_ = lean_array_size(v_decls_1003_);
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_998_, v_sz_1008_, v___x_1009_, v_decls_1003_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v___x_1010_);
v___x_1012_ = v___x_1006_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_givenNames_1002_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_valueMap_1004_);
v___x_1012_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_st_ref_put(v_a_999_, v___x_1012_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(lean_object* v_fvarId_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec(v_fvarId_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet(lean_object* v_fvarId_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_1022_, v_a_1025_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_ensureIsLet___boxed(lean_object* v_fvarId_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Meta_ExtractLets_ensureIsLet(v_fvarId_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_fvarId_1032_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(size_t v_sz_1042_, size_t v_i_1043_, lean_object* v_bs_1044_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_usize_dec_lt(v_i_1043_, v_sz_1042_);
if (v___x_1045_ == 0)
{
return v_bs_1044_;
}
else
{
lean_object* v_v_1046_; lean_object* v_decl_1047_; lean_object* v___x_1048_; lean_object* v_bs_x27_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v_v_1046_ = lean_array_uget_borrowed(v_bs_1044_, v_i_1043_);
v_decl_1047_ = lean_ctor_get(v_v_1046_, 0);
lean_inc_ref(v_decl_1047_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v_bs_x27_1049_ = lean_array_uset(v_bs_1044_, v_i_1043_, v___x_1048_);
v___x_1050_ = ((size_t)1ULL);
v___x_1051_ = lean_usize_add(v_i_1043_, v___x_1050_);
v___x_1052_ = lean_array_uset(v_bs_x27_1049_, v_i_1043_, v_decl_1047_);
v_i_1043_ = v___x_1051_;
v_bs_1044_ = v___x_1052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1___boxed(lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_bs_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_boxed_1057_, v_i_boxed_1058_, v_bs_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(lean_object* v_x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
lean_inc(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
v___x_1069_ = lean_apply_8(v_x_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, lean_box(0));
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(v_x_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(lean_object* v_decls_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; 
lean_inc(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1090_, 0, v_x_1081_);
lean_closure_set(v___f_1090_, 1, v___y_1082_);
lean_closure_set(v___f_1090_, 2, v___y_1083_);
lean_closure_set(v___f_1090_, 3, v___y_1084_);
v___x_1091_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1080_, v___f_1090_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1091_) == 0)
{
return v___x_1091_;
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___boxed(lean_object* v_decls_1100_, lean_object* v_x_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1100_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(lean_object* v___x_1111_, lean_object* v_as_1112_, size_t v_i_1113_, size_t v_stop_1114_, lean_object* v_b_1115_){
_start:
{
lean_object* v___y_1117_; uint8_t v___x_1121_; 
v___x_1121_ = lean_usize_dec_eq(v_i_1113_, v_stop_1114_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v_decl_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1122_ = lean_array_uget_borrowed(v_as_1112_, v_i_1113_);
v_decl_1123_ = lean_ctor_get(v___x_1122_, 0);
v___x_1124_ = l_Lean_LocalDecl_fvarId(v_decl_1123_);
v___x_1125_ = l_Lean_LocalContext_contains(v___x_1111_, v___x_1124_);
lean_dec(v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_inc(v___x_1122_);
v___x_1126_ = lean_array_push(v_b_1115_, v___x_1122_);
v___y_1117_ = v___x_1126_;
goto v___jp_1116_;
}
else
{
v___y_1117_ = v_b_1115_;
goto v___jp_1116_;
}
}
else
{
return v_b_1115_;
}
v___jp_1116_:
{
size_t v___x_1118_; size_t v___x_1119_; 
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1113_, v___x_1118_);
v_i_1113_ = v___x_1119_;
v_b_1115_ = v___y_1117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(lean_object* v___x_1127_, lean_object* v_as_1128_, lean_object* v_i_1129_, lean_object* v_stop_1130_, lean_object* v_b_1131_){
_start:
{
size_t v_i_boxed_1132_; size_t v_stop_boxed_1133_; lean_object* v_res_1134_; 
v_i_boxed_1132_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_stop_boxed_1133_ = lean_unbox_usize(v_stop_1130_);
lean_dec(v_stop_1130_);
v_res_1134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_1127_, v_as_1128_, v_i_boxed_1132_, v_stop_boxed_1133_, v_b_1131_);
lean_dec_ref(v_as_1128_);
lean_dec_ref(v___x_1127_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(lean_object* v_decls_1135_, lean_object* v_k_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___y_1146_; lean_object* v_lctx_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_lctx_1152_ = lean_ctor_get(v___y_1140_, 2);
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = lean_array_get_size(v_decls_1135_);
v___x_1155_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_1156_ = lean_nat_dec_lt(v___x_1153_, v___x_1154_);
if (v___x_1156_ == 0)
{
v___y_1146_ = v___x_1155_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_nat_dec_le(v___x_1154_, v___x_1154_);
if (v___x_1157_ == 0)
{
if (v___x_1156_ == 0)
{
v___y_1146_ = v___x_1155_;
goto v___jp_1145_;
}
else
{
size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = ((size_t)0ULL);
v___x_1159_ = lean_usize_of_nat(v___x_1154_);
v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1152_, v_decls_1135_, v___x_1158_, v___x_1159_, v___x_1155_);
v___y_1146_ = v___x_1160_;
goto v___jp_1145_;
}
}
else
{
size_t v___x_1161_; size_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = ((size_t)0ULL);
v___x_1162_ = lean_usize_of_nat(v___x_1154_);
v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_1152_, v_decls_1135_, v___x_1161_, v___x_1162_, v___x_1155_);
v___y_1146_ = v___x_1163_;
goto v___jp_1145_;
}
}
v___jp_1145_:
{
size_t v_sz_1147_; size_t v___x_1148_; lean_object* v_decls_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_sz_1147_ = lean_array_size(v___y_1146_);
v___x_1148_ = ((size_t)0ULL);
v_decls_1149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_1147_, v___x_1148_, v___y_1146_);
v___x_1150_ = lean_array_to_list(v_decls_1149_);
v___x_1151_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v___x_1150_, v_k_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(lean_object* v_decls_1164_, lean_object* v_k_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1164_, v_k_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec_ref(v_decls_1164_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_fvarId_1175_, lean_object* v_as_1176_, lean_object* v_j_1177_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_array_get_size(v_as_1176_);
v___x_1179_ = lean_nat_dec_lt(v_j_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_dec(v_j_1177_);
v___x_1180_ = lean_box(0);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v_decl_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1181_ = lean_array_fget_borrowed(v_as_1176_, v_j_1177_);
v_decl_1182_ = lean_ctor_get(v___x_1181_, 0);
v___x_1183_ = l_Lean_LocalDecl_fvarId(v_decl_1182_);
v___x_1184_ = l_Lean_instBEqFVarId_beq(v___x_1183_, v_fvarId_1175_);
lean_dec(v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_nat_add(v_j_1177_, v___x_1185_);
lean_dec(v_j_1177_);
v_j_1177_ = v___x_1186_;
goto _start;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_j_1177_);
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_fvarId_1189_, lean_object* v_as_1190_, lean_object* v_j_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1189_, v_as_1190_, v_j_1191_);
lean_dec_ref(v_as_1190_);
lean_dec(v_fvarId_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg(lean_object* v_fvarId_1193_, lean_object* v_k_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v_lctx_1204_; uint8_t v___x_1205_; 
v___x_1203_ = lean_st_ref_get(v_a_1197_);
v_lctx_1204_ = lean_ctor_get(v_a_1198_, 2);
v___x_1205_ = l_Lean_LocalContext_contains(v_lctx_1204_, v_fvarId_1193_);
if (v___x_1205_ == 0)
{
lean_object* v_decls_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_decls_1206_ = lean_ctor_get(v___x_1203_, 1);
lean_inc_ref(v_decls_1206_);
lean_dec(v___x_1203_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_fvarId_1193_, v_decls_1206_, v___x_1207_);
if (lean_obj_tag(v___x_1208_) == 1)
{
lean_object* v_val_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_val_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_val_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_add(v_val_1209_, v___x_1210_);
lean_dec(v_val_1209_);
v___x_1212_ = l_Array_toSubarray___redArg(v_decls_1206_, v___x_1207_, v___x_1211_);
v___x_1213_ = l_Subarray_copy___redArg(v___x_1212_);
v___x_1214_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_1213_, v_k_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec_ref(v___x_1213_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; 
lean_dec(v___x_1208_);
lean_dec_ref(v_decls_1206_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
lean_inc(v_a_1197_);
lean_inc(v_a_1196_);
lean_inc_ref(v_a_1195_);
v___x_1215_ = lean_apply_8(v_k_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, lean_box(0));
return v___x_1215_;
}
}
else
{
lean_object* v___x_1216_; 
lean_dec(v___x_1203_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
lean_inc(v_a_1197_);
lean_inc(v_a_1196_);
lean_inc_ref(v_a_1195_);
v___x_1216_ = lean_apply_8(v_k_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, lean_box(0));
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(lean_object* v_fvarId_1217_, lean_object* v_k_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1217_, v_k_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_fvarId_1217_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1228_, lean_object* v_fvarId_1229_, lean_object* v_k_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1229_, v_k_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_fvarId_1241_, lean_object* v_k_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1240_, v_fvarId_1241_, v_k_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_fvarId_1241_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(lean_object* v_00_u03b1_1252_, lean_object* v_decls_1253_, lean_object* v_x_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_1253_, v_x_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_decls_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_1264_, v_decls_1265_, v_x_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(lean_object* v_00_u03b1_1276_, lean_object* v_decls_1277_, lean_object* v_k_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_1277_, v_k_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_decls_1289_, lean_object* v_k_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_1288_, v_decls_1289_, v_k_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec_ref(v_decls_1289_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(lean_object* v_e_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v___x_1303_; 
v___x_1303_ = l_Lean_Expr_hasMVar(v_e_1300_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_e_1300_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; lean_object* v_mctx_1306_; lean_object* v___x_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; lean_object* v___x_1310_; lean_object* v_cache_1311_; lean_object* v_zetaDeltaFVarIds_1312_; lean_object* v_postponed_1313_; lean_object* v_diag_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1323_; 
v___x_1305_ = lean_st_ref_get(v___y_1301_);
v_mctx_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_mctx_1306_);
lean_dec(v___x_1305_);
v___x_1307_ = l_Lean_instantiateMVarsCore(v_mctx_1306_, v_e_1300_);
v_fst_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_fst_1308_);
v_snd_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_snd_1309_);
lean_dec_ref(v___x_1307_);
v___x_1310_ = lean_st_ref_take(v___y_1301_);
v_cache_1311_ = lean_ctor_get(v___x_1310_, 1);
v_zetaDeltaFVarIds_1312_ = lean_ctor_get(v___x_1310_, 2);
v_postponed_1313_ = lean_ctor_get(v___x_1310_, 3);
v_diag_1314_ = lean_ctor_get(v___x_1310_, 4);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1310_, 0);
lean_dec(v_unused_1324_);
v___x_1316_ = v___x_1310_;
v_isShared_1317_ = v_isSharedCheck_1323_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_diag_1314_);
lean_inc(v_postponed_1313_);
lean_inc(v_zetaDeltaFVarIds_1312_);
lean_inc(v_cache_1311_);
lean_dec(v___x_1310_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1323_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_snd_1309_);
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_snd_1309_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_cache_1311_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_zetaDeltaFVarIds_1312_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_postponed_1313_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_diag_1314_);
v___x_1319_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_st_ref_put(v___y_1301_, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_fst_1308_);
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(lean_object* v_e_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1325_, v___y_1326_);
lean_dec(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(lean_object* v_e_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_1329_, v___y_1334_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(lean_object* v_e_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(v_e_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(lean_object* v_as_1349_, size_t v_i_1350_, size_t v_stop_1351_, lean_object* v_b_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_a_1362_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v_i_1382_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v_i_1409_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; uint8_t v___x_1430_; 
v___x_1430_ = lean_usize_dec_eq(v_i_1350_, v_stop_1351_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_array_uget_borrowed(v_as_1349_, v_i_1350_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_box(0);
v_a_1362_ = v___x_1432_;
goto v___jp_1361_;
}
else
{
lean_object* v_val_1433_; uint8_t v___y_1435_; uint8_t v___x_1483_; 
v_val_1433_ = lean_ctor_get(v___x_1431_, 0);
v___x_1483_ = l_Lean_LocalDecl_isLet(v_val_1433_, v___x_1430_);
if (v___x_1483_ == 0)
{
v___y_1435_ = v___x_1483_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1484_; 
v___x_1484_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1433_);
if (v___x_1484_ == 0)
{
v___y_1435_ = v___x_1483_;
goto v___jp_1434_;
}
else
{
goto v___jp_1366_;
}
}
v___jp_1434_:
{
if (v___y_1435_ == 0)
{
goto v___jp_1366_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = l_Lean_LocalDecl_value(v_val_1433_, v___x_1430_);
v___x_1437_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1436_, v___y_1357_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v_givenNames_1440_; lean_object* v_decls_1441_; lean_object* v_valueMap_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = lean_st_ref_take(v___y_1355_);
v_givenNames_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_givenNames_1440_);
v_decls_1441_ = lean_ctor_get(v___x_1439_, 1);
lean_inc_ref(v_decls_1441_);
v_valueMap_1442_ = lean_ctor_get(v___x_1439_, 2);
lean_inc_ref(v_valueMap_1442_);
lean_dec(v___x_1439_);
v___x_1443_ = lean_box(0);
v___x_1444_ = l_Lean_LocalDecl_fvarId(v_val_1433_);
v___x_1445_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1442_, v_a_1438_);
switch(lean_obj_tag(v___x_1445_))
{
case 0:
{
lean_object* v_index_1446_; lean_object* v_size_1447_; lean_object* v___x_1448_; 
v_index_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_index_1446_);
lean_dec_ref_known(v___x_1445_, 3);
v_size_1447_ = lean_ctor_get(v_valueMap_1442_, 0);
lean_inc(v_size_1447_);
v___x_1448_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_1442_, v_size_1447_, v_index_1446_, v_a_1438_, v___x_1444_);
lean_dec(v_index_1446_);
v___y_1369_ = v_decls_1441_;
v___y_1370_ = v_givenNames_1440_;
v___y_1371_ = v___x_1443_;
v___y_1372_ = v___x_1448_;
goto v___jp_1368_;
}
case 1:
{
lean_object* v_index_1449_; lean_object* v_size_1450_; lean_object* v_keyArray_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_index_1449_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_index_1449_);
lean_dec_ref_known(v___x_1445_, 1);
v_size_1450_ = lean_ctor_get(v_valueMap_1442_, 0);
v_keyArray_1451_ = lean_ctor_get(v_valueMap_1442_, 1);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_size_1450_, v___x_1452_);
v___x_1454_ = lean_array_get_size(v_keyArray_1451_);
v___x_1455_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec(v___x_1453_);
lean_dec(v_index_1449_);
v___y_1415_ = v_decls_1441_;
v___y_1416_ = v_givenNames_1440_;
v___y_1417_ = v_valueMap_1442_;
v___y_1418_ = v___x_1443_;
v___y_1419_ = v___x_1444_;
v___y_1420_ = v_a_1438_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1456_ = lean_unsigned_to_nat(4u);
v___x_1457_ = lean_nat_mul(v___x_1453_, v___x_1456_);
v___x_1458_ = lean_unsigned_to_nat(3u);
v___x_1459_ = lean_nat_mul(v___x_1454_, v___x_1458_);
v___x_1460_ = lean_nat_dec_le(v___x_1457_, v___x_1459_);
lean_dec(v___x_1459_);
lean_dec(v___x_1457_);
if (v___x_1460_ == 0)
{
lean_dec(v___x_1453_);
lean_dec(v_index_1449_);
v___y_1415_ = v_decls_1441_;
v___y_1416_ = v_givenNames_1440_;
v___y_1417_ = v_valueMap_1442_;
v___y_1418_ = v___x_1443_;
v___y_1419_ = v___x_1444_;
v___y_1420_ = v_a_1438_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_1442_, v___x_1453_, v_index_1449_, v_a_1438_, v___x_1444_);
lean_dec(v_index_1449_);
v___y_1369_ = v_decls_1441_;
v___y_1370_ = v_givenNames_1440_;
v___y_1371_ = v___x_1443_;
v___y_1372_ = v___x_1461_;
goto v___jp_1368_;
}
}
}
default: 
{
lean_object* v_size_1462_; lean_object* v_keyArray_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_size_1462_ = lean_ctor_get(v_valueMap_1442_, 0);
v_keyArray_1463_ = lean_ctor_get(v_valueMap_1442_, 1);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_size_1462_, v___x_1464_);
v___x_1466_ = lean_array_get_size(v_keyArray_1463_);
v___x_1467_ = lean_nat_dec_lt(v___x_1465_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec(v___x_1465_);
v___x_1468_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_valueMap_1442_);
lean_dec_ref(v_valueMap_1442_);
v___y_1388_ = v_decls_1441_;
v___y_1389_ = v_givenNames_1440_;
v___y_1390_ = v___x_1443_;
v___y_1391_ = v___x_1444_;
v___y_1392_ = v_a_1438_;
v___y_1393_ = v___x_1468_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1469_ = lean_unsigned_to_nat(4u);
v___x_1470_ = lean_nat_mul(v___x_1465_, v___x_1469_);
lean_dec(v___x_1465_);
v___x_1471_ = lean_unsigned_to_nat(3u);
v___x_1472_ = lean_nat_mul(v___x_1466_, v___x_1471_);
v___x_1473_ = lean_nat_dec_le(v___x_1470_, v___x_1472_);
lean_dec(v___x_1472_);
lean_dec(v___x_1470_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_valueMap_1442_);
lean_dec_ref(v_valueMap_1442_);
v___y_1388_ = v_decls_1441_;
v___y_1389_ = v_givenNames_1440_;
v___y_1390_ = v___x_1443_;
v___y_1391_ = v___x_1444_;
v___y_1392_ = v_a_1438_;
v___y_1393_ = v___x_1474_;
goto v___jp_1387_;
}
else
{
v___y_1388_ = v_decls_1441_;
v___y_1389_ = v_givenNames_1440_;
v___y_1390_ = v___x_1443_;
v___y_1391_ = v___x_1444_;
v___y_1392_ = v_a_1438_;
v___y_1393_ = v_valueMap_1442_;
goto v___jp_1387_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1437_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1437_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_b_1352_);
return v___x_1485_;
}
v___jp_1361_:
{
size_t v___x_1363_; size_t v___x_1364_; 
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1350_, v___x_1363_);
v_i_1350_ = v___x_1364_;
v_b_1352_ = v_a_1362_;
goto _start;
}
v___jp_1366_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_box(0);
v_a_1362_ = v___x_1367_;
goto v___jp_1361_;
}
v___jp_1368_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1370_);
lean_ctor_set(v___x_1373_, 1, v___y_1369_);
lean_ctor_set(v___x_1373_, 2, v___y_1372_);
v___x_1374_ = lean_st_ref_put(v___y_1355_, v___x_1373_);
v_a_1362_ = v___y_1371_;
goto v___jp_1361_;
}
v___jp_1375_:
{
lean_object* v_size_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_size_1383_ = lean_ctor_get(v___y_1380_, 0);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_size_1383_, v___x_1384_);
v___x_1386_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1380_, v___x_1385_, v_i_1382_, v___y_1381_, v___y_1379_);
lean_dec(v_i_1382_);
v___y_1369_ = v___y_1376_;
v___y_1370_ = v___y_1377_;
v___y_1371_ = v___y_1378_;
v___y_1372_ = v___x_1386_;
goto v___jp_1368_;
}
v___jp_1387_:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v___y_1393_, v___y_1392_);
switch(lean_obj_tag(v___x_1394_))
{
case 0:
{
lean_object* v_index_1395_; lean_object* v_size_1396_; lean_object* v___x_1397_; 
v_index_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_index_1395_);
lean_dec_ref_known(v___x_1394_, 3);
v_size_1396_ = lean_ctor_get(v___y_1393_, 0);
lean_inc(v_size_1396_);
v___x_1397_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1393_, v_size_1396_, v_index_1395_, v___y_1392_, v___y_1391_);
lean_dec(v_index_1395_);
v___y_1369_ = v___y_1388_;
v___y_1370_ = v___y_1389_;
v___y_1371_ = v___y_1390_;
v___y_1372_ = v___x_1397_;
goto v___jp_1368_;
}
case 1:
{
lean_object* v_index_1398_; 
v_index_1398_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_index_1398_);
lean_dec_ref_known(v___x_1394_, 1);
v___y_1376_ = v___y_1388_;
v___y_1377_ = v___y_1389_;
v___y_1378_ = v___y_1390_;
v___y_1379_ = v___y_1391_;
v___y_1380_ = v___y_1393_;
v___y_1381_ = v___y_1392_;
v_i_1382_ = v_index_1398_;
goto v___jp_1375_;
}
default: 
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1393_, v___x_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_index_1401_; 
v_index_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_index_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___y_1376_ = v___y_1388_;
v___y_1377_ = v___y_1389_;
v___y_1378_ = v___y_1390_;
v___y_1379_ = v___y_1391_;
v___y_1380_ = v___y_1393_;
v___y_1381_ = v___y_1392_;
v_i_1382_ = v_index_1401_;
goto v___jp_1375_;
}
else
{
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
v___y_1369_ = v___y_1388_;
v___y_1370_ = v___y_1389_;
v___y_1371_ = v___y_1390_;
v___y_1372_ = v___y_1393_;
goto v___jp_1368_;
}
}
}
}
v___jp_1402_:
{
lean_object* v_size_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_size_1410_ = lean_ctor_get(v___y_1408_, 0);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_add(v_size_1410_, v___x_1411_);
v___x_1413_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1408_, v___x_1412_, v_i_1409_, v___y_1407_, v___y_1406_);
lean_dec(v_i_1409_);
v___y_1369_ = v___y_1403_;
v___y_1370_ = v___y_1404_;
v___y_1371_ = v___y_1405_;
v___y_1372_ = v___x_1413_;
goto v___jp_1368_;
}
v___jp_1414_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v___y_1417_);
lean_dec_ref(v___y_1417_);
v___x_1422_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v___x_1421_, v___y_1420_);
switch(lean_obj_tag(v___x_1422_))
{
case 0:
{
lean_object* v_index_1423_; lean_object* v_size_1424_; lean_object* v___x_1425_; 
v_index_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_index_1423_);
lean_dec_ref_known(v___x_1422_, 3);
v_size_1424_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_size_1424_);
v___x_1425_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1421_, v_size_1424_, v_index_1423_, v___y_1420_, v___y_1419_);
lean_dec(v_index_1423_);
v___y_1369_ = v___y_1415_;
v___y_1370_ = v___y_1416_;
v___y_1371_ = v___y_1418_;
v___y_1372_ = v___x_1425_;
goto v___jp_1368_;
}
case 1:
{
lean_object* v_index_1426_; 
v_index_1426_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_index_1426_);
lean_dec_ref_known(v___x_1422_, 1);
v___y_1403_ = v___y_1415_;
v___y_1404_ = v___y_1416_;
v___y_1405_ = v___y_1418_;
v___y_1406_ = v___y_1419_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v___x_1421_;
v_i_1409_ = v_index_1426_;
goto v___jp_1402_;
}
default: 
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1421_, v___x_1427_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_index_1429_; 
v_index_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_index_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___y_1403_ = v___y_1415_;
v___y_1404_ = v___y_1416_;
v___y_1405_ = v___y_1418_;
v___y_1406_ = v___y_1419_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v___x_1421_;
v_i_1409_ = v_index_1429_;
goto v___jp_1402_;
}
else
{
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
v___y_1369_ = v___y_1415_;
v___y_1370_ = v___y_1416_;
v___y_1371_ = v___y_1418_;
v___y_1372_ = v___x_1421_;
goto v___jp_1368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_as_1486_, lean_object* v_i_1487_, lean_object* v_stop_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
size_t v_i_boxed_1498_; size_t v_stop_boxed_1499_; lean_object* v_res_1500_; 
v_i_boxed_1498_ = lean_unbox_usize(v_i_1487_);
lean_dec(v_i_1487_);
v_stop_boxed_1499_ = lean_unbox_usize(v_stop_1488_);
lean_dec(v_stop_1488_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1486_, v_i_boxed_1498_, v_stop_boxed_1499_, v_b_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec_ref(v_as_1486_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(lean_object* v_as_1501_, size_t v_i_1502_, size_t v_stop_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_a_1514_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v_i_1534_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v_i_1561_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; uint8_t v___x_1582_; 
v___x_1582_ = lean_usize_dec_eq(v_i_1502_, v_stop_1503_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_array_uget_borrowed(v_as_1501_, v_i_1502_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_box(0);
v_a_1514_ = v___x_1584_;
goto v___jp_1513_;
}
else
{
lean_object* v_val_1585_; uint8_t v___y_1587_; uint8_t v___x_1635_; 
v_val_1585_ = lean_ctor_get(v___x_1583_, 0);
v___x_1635_ = l_Lean_LocalDecl_isLet(v_val_1585_, v___x_1582_);
if (v___x_1635_ == 0)
{
v___y_1587_ = v___x_1635_;
goto v___jp_1586_;
}
else
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1585_);
if (v___x_1636_ == 0)
{
v___y_1587_ = v___x_1635_;
goto v___jp_1586_;
}
else
{
goto v___jp_1518_;
}
}
v___jp_1586_:
{
if (v___y_1587_ == 0)
{
goto v___jp_1518_;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = l_Lean_LocalDecl_value(v_val_1585_, v___x_1582_);
v___x_1589_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_1588_, v___y_1509_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v_givenNames_1592_; lean_object* v_decls_1593_; lean_object* v_valueMap_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = lean_st_ref_take(v___y_1507_);
v_givenNames_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_givenNames_1592_);
v_decls_1593_ = lean_ctor_get(v___x_1591_, 1);
lean_inc_ref(v_decls_1593_);
v_valueMap_1594_ = lean_ctor_get(v___x_1591_, 2);
lean_inc_ref(v_valueMap_1594_);
lean_dec(v___x_1591_);
v___x_1595_ = lean_box(0);
v___x_1596_ = l_Lean_LocalDecl_fvarId(v_val_1585_);
v___x_1597_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_1594_, v_a_1590_);
switch(lean_obj_tag(v___x_1597_))
{
case 0:
{
lean_object* v_index_1598_; lean_object* v_size_1599_; lean_object* v___x_1600_; 
v_index_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_index_1598_);
lean_dec_ref_known(v___x_1597_, 3);
v_size_1599_ = lean_ctor_get(v_valueMap_1594_, 0);
lean_inc(v_size_1599_);
v___x_1600_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_1594_, v_size_1599_, v_index_1598_, v_a_1590_, v___x_1596_);
lean_dec(v_index_1598_);
v___y_1521_ = v___x_1595_;
v___y_1522_ = v_givenNames_1592_;
v___y_1523_ = v_decls_1593_;
v___y_1524_ = v___x_1600_;
goto v___jp_1520_;
}
case 1:
{
lean_object* v_index_1601_; lean_object* v_size_1602_; lean_object* v_keyArray_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v_index_1601_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_index_1601_);
lean_dec_ref_known(v___x_1597_, 1);
v_size_1602_ = lean_ctor_get(v_valueMap_1594_, 0);
v_keyArray_1603_ = lean_ctor_get(v_valueMap_1594_, 1);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_add(v_size_1602_, v___x_1604_);
v___x_1606_ = lean_array_get_size(v_keyArray_1603_);
v___x_1607_ = lean_nat_dec_lt(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_dec(v___x_1605_);
lean_dec(v_index_1601_);
v___y_1567_ = v___x_1595_;
v___y_1568_ = v_givenNames_1592_;
v___y_1569_ = v_decls_1593_;
v___y_1570_ = v___x_1596_;
v___y_1571_ = v_a_1590_;
v___y_1572_ = v_valueMap_1594_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1608_ = lean_unsigned_to_nat(4u);
v___x_1609_ = lean_nat_mul(v___x_1605_, v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(3u);
v___x_1611_ = lean_nat_mul(v___x_1606_, v___x_1610_);
v___x_1612_ = lean_nat_dec_le(v___x_1609_, v___x_1611_);
lean_dec(v___x_1611_);
lean_dec(v___x_1609_);
if (v___x_1612_ == 0)
{
lean_dec(v___x_1605_);
lean_dec(v_index_1601_);
v___y_1567_ = v___x_1595_;
v___y_1568_ = v_givenNames_1592_;
v___y_1569_ = v_decls_1593_;
v___y_1570_ = v___x_1596_;
v___y_1571_ = v_a_1590_;
v___y_1572_ = v_valueMap_1594_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_DHashMap_Raw_setEntry___redArg(v_valueMap_1594_, v___x_1605_, v_index_1601_, v_a_1590_, v___x_1596_);
lean_dec(v_index_1601_);
v___y_1521_ = v___x_1595_;
v___y_1522_ = v_givenNames_1592_;
v___y_1523_ = v_decls_1593_;
v___y_1524_ = v___x_1613_;
goto v___jp_1520_;
}
}
}
default: 
{
lean_object* v_size_1614_; lean_object* v_keyArray_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v_size_1614_ = lean_ctor_get(v_valueMap_1594_, 0);
v_keyArray_1615_ = lean_ctor_get(v_valueMap_1594_, 1);
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = lean_nat_add(v_size_1614_, v___x_1616_);
v___x_1618_ = lean_array_get_size(v_keyArray_1615_);
v___x_1619_ = lean_nat_dec_lt(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec(v___x_1617_);
v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_valueMap_1594_);
lean_dec_ref(v_valueMap_1594_);
v___y_1540_ = v___x_1595_;
v___y_1541_ = v_givenNames_1592_;
v___y_1542_ = v_decls_1593_;
v___y_1543_ = v___x_1596_;
v___y_1544_ = v_a_1590_;
v___y_1545_ = v___x_1620_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1621_ = lean_unsigned_to_nat(4u);
v___x_1622_ = lean_nat_mul(v___x_1617_, v___x_1621_);
lean_dec(v___x_1617_);
v___x_1623_ = lean_unsigned_to_nat(3u);
v___x_1624_ = lean_nat_mul(v___x_1618_, v___x_1623_);
v___x_1625_ = lean_nat_dec_le(v___x_1622_, v___x_1624_);
lean_dec(v___x_1624_);
lean_dec(v___x_1622_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v_valueMap_1594_);
lean_dec_ref(v_valueMap_1594_);
v___y_1540_ = v___x_1595_;
v___y_1541_ = v_givenNames_1592_;
v___y_1542_ = v_decls_1593_;
v___y_1543_ = v___x_1596_;
v___y_1544_ = v_a_1590_;
v___y_1545_ = v___x_1626_;
goto v___jp_1539_;
}
else
{
v___y_1540_ = v___x_1595_;
v___y_1541_ = v_givenNames_1592_;
v___y_1542_ = v_decls_1593_;
v___y_1543_ = v___x_1596_;
v___y_1544_ = v_a_1590_;
v___y_1545_ = v_valueMap_1594_;
goto v___jp_1539_;
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_a_1627_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1589_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1589_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_b_1504_);
return v___x_1637_;
}
v___jp_1513_:
{
size_t v___x_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_add(v_i_1502_, v___x_1515_);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_1501_, v___x_1516_, v_stop_1503_, v_a_1514_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1517_;
}
v___jp_1518_:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_box(0);
v_a_1514_ = v___x_1519_;
goto v___jp_1513_;
}
v___jp_1520_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1525_, 0, v___y_1522_);
lean_ctor_set(v___x_1525_, 1, v___y_1523_);
lean_ctor_set(v___x_1525_, 2, v___y_1524_);
v___x_1526_ = lean_st_ref_put(v___y_1507_, v___x_1525_);
v_a_1514_ = v___y_1521_;
goto v___jp_1513_;
}
v___jp_1527_:
{
lean_object* v_size_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_size_1535_ = lean_ctor_get(v___y_1532_, 0);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_add(v_size_1535_, v___x_1536_);
v___x_1538_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1532_, v___x_1537_, v_i_1534_, v___y_1533_, v___y_1531_);
lean_dec(v_i_1534_);
v___y_1521_ = v___y_1528_;
v___y_1522_ = v___y_1529_;
v___y_1523_ = v___y_1530_;
v___y_1524_ = v___x_1538_;
goto v___jp_1520_;
}
v___jp_1539_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v___y_1545_, v___y_1544_);
switch(lean_obj_tag(v___x_1546_))
{
case 0:
{
lean_object* v_index_1547_; lean_object* v_size_1548_; lean_object* v___x_1549_; 
v_index_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_index_1547_);
lean_dec_ref_known(v___x_1546_, 3);
v_size_1548_ = lean_ctor_get(v___y_1545_, 0);
lean_inc(v_size_1548_);
v___x_1549_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1545_, v_size_1548_, v_index_1547_, v___y_1544_, v___y_1543_);
lean_dec(v_index_1547_);
v___y_1521_ = v___y_1540_;
v___y_1522_ = v___y_1541_;
v___y_1523_ = v___y_1542_;
v___y_1524_ = v___x_1549_;
goto v___jp_1520_;
}
case 1:
{
lean_object* v_index_1550_; 
v_index_1550_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_index_1550_);
lean_dec_ref_known(v___x_1546_, 1);
v___y_1528_ = v___y_1540_;
v___y_1529_ = v___y_1541_;
v___y_1530_ = v___y_1542_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1545_;
v___y_1533_ = v___y_1544_;
v_i_1534_ = v_index_1550_;
goto v___jp_1527_;
}
default: 
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1545_, v___x_1551_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_index_1553_; 
v_index_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_index_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___y_1528_ = v___y_1540_;
v___y_1529_ = v___y_1541_;
v___y_1530_ = v___y_1542_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1545_;
v___y_1533_ = v___y_1544_;
v_i_1534_ = v_index_1553_;
goto v___jp_1527_;
}
else
{
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
v___y_1521_ = v___y_1540_;
v___y_1522_ = v___y_1541_;
v___y_1523_ = v___y_1542_;
v___y_1524_ = v___y_1545_;
goto v___jp_1520_;
}
}
}
}
v___jp_1554_:
{
lean_object* v_size_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_size_1562_ = lean_ctor_get(v___y_1556_, 0);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_add(v_size_1562_, v___x_1563_);
v___x_1565_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1556_, v___x_1564_, v_i_1561_, v___y_1560_, v___y_1559_);
lean_dec(v_i_1561_);
v___y_1521_ = v___y_1555_;
v___y_1522_ = v___y_1557_;
v___y_1523_ = v___y_1558_;
v___y_1524_ = v___x_1565_;
goto v___jp_1520_;
}
v___jp_1566_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_addDecl_spec__1___redArg(v___y_1572_);
lean_dec_ref(v___y_1572_);
v___x_1574_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v___x_1573_, v___y_1571_);
switch(lean_obj_tag(v___x_1574_))
{
case 0:
{
lean_object* v_index_1575_; lean_object* v_size_1576_; lean_object* v___x_1577_; 
v_index_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_index_1575_);
lean_dec_ref_known(v___x_1574_, 3);
v_size_1576_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_size_1576_);
v___x_1577_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1573_, v_size_1576_, v_index_1575_, v___y_1571_, v___y_1570_);
lean_dec(v_index_1575_);
v___y_1521_ = v___y_1567_;
v___y_1522_ = v___y_1568_;
v___y_1523_ = v___y_1569_;
v___y_1524_ = v___x_1577_;
goto v___jp_1520_;
}
case 1:
{
lean_object* v_index_1578_; 
v_index_1578_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_index_1578_);
lean_dec_ref_known(v___x_1574_, 1);
v___y_1555_ = v___y_1567_;
v___y_1556_ = v___x_1573_;
v___y_1557_ = v___y_1568_;
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___y_1570_;
v___y_1560_ = v___y_1571_;
v_i_1561_ = v_index_1578_;
goto v___jp_1554_;
}
default: 
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1573_, v___x_1579_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_index_1581_; 
v_index_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_index_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___y_1555_ = v___y_1567_;
v___y_1556_ = v___x_1573_;
v___y_1557_ = v___y_1568_;
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___y_1570_;
v___y_1560_ = v___y_1571_;
v_i_1561_ = v_index_1581_;
goto v___jp_1554_;
}
else
{
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
v___y_1521_ = v___y_1567_;
v___y_1522_ = v___y_1568_;
v___y_1523_ = v___y_1569_;
v___y_1524_ = v___x_1573_;
goto v___jp_1520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1638_, lean_object* v_i_1639_, lean_object* v_stop_1640_, lean_object* v_b_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
size_t v_i_boxed_1650_; size_t v_stop_boxed_1651_; lean_object* v_res_1652_; 
v_i_boxed_1650_ = lean_unbox_usize(v_i_1639_);
lean_dec(v_i_1639_);
v_stop_boxed_1651_ = lean_unbox_usize(v_stop_1640_);
lean_dec(v_stop_1640_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_1638_, v_i_boxed_1650_, v_stop_boxed_1651_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v_as_1638_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
if (lean_obj_tag(v_x_1653_) == 0)
{
lean_object* v_cs_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1683_; 
v_cs_1662_ = lean_ctor_get(v_x_1653_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1664_ = v_x_1653_;
v_isShared_1665_ = v_isSharedCheck_1683_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_cs_1662_);
lean_dec(v_x_1653_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1683_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_array_get_size(v_cs_1662_);
v___x_1668_ = lean_box(0);
v___x_1669_ = lean_nat_dec_lt(v___x_1666_, v___x_1667_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1671_; 
lean_dec_ref(v_cs_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1668_);
v___x_1671_ = v___x_1664_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1668_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
else
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_nat_dec_le(v___x_1667_, v___x_1667_);
if (v___x_1673_ == 0)
{
if (v___x_1669_ == 0)
{
lean_object* v___x_1675_; 
lean_dec_ref(v_cs_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1668_);
v___x_1675_ = v___x_1664_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1668_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
lean_del_object(v___x_1664_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = lean_usize_of_nat(v___x_1667_);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1662_, v___x_1677_, v___x_1678_, v___x_1668_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec_ref(v_cs_1662_);
return v___x_1679_;
}
}
else
{
size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
lean_del_object(v___x_1664_);
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = lean_usize_of_nat(v___x_1667_);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1662_, v___x_1680_, v___x_1681_, v___x_1668_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec_ref(v_cs_1662_);
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_vs_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1705_; 
v_vs_1684_ = lean_ctor_get(v_x_1653_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1686_ = v_x_1653_;
v_isShared_1687_ = v_isSharedCheck_1705_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_vs_1684_);
lean_dec(v_x_1653_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1705_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = lean_array_get_size(v_vs_1684_);
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_nat_dec_lt(v___x_1688_, v___x_1689_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1693_; 
lean_dec_ref(v_vs_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1690_);
v___x_1693_ = v___x_1686_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
else
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_nat_dec_le(v___x_1689_, v___x_1689_);
if (v___x_1695_ == 0)
{
if (v___x_1691_ == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref(v_vs_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1690_);
v___x_1697_ = v___x_1686_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1690_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
size_t v___x_1699_; size_t v___x_1700_; lean_object* v___x_1701_; 
lean_del_object(v___x_1686_);
v___x_1699_ = ((size_t)0ULL);
v___x_1700_ = lean_usize_of_nat(v___x_1689_);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1684_, v___x_1699_, v___x_1700_, v___x_1690_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec_ref(v_vs_1684_);
return v___x_1701_;
}
}
else
{
size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1686_);
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = lean_usize_of_nat(v___x_1689_);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1684_, v___x_1702_, v___x_1703_, v___x_1690_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec_ref(v_vs_1684_);
return v___x_1704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(lean_object* v_as_1706_, size_t v_i_1707_, size_t v_stop_1708_, lean_object* v_b_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_eq(v_i_1707_, v_stop_1708_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_array_uget_borrowed(v_as_1706_, v_i_1707_);
lean_inc(v___x_1719_);
v___x_1720_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_1719_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; size_t v___x_1722_; size_t v___x_1723_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1707_, v___x_1722_);
v_i_1707_ = v___x_1723_;
v_b_1709_ = v_a_1721_;
goto _start;
}
else
{
return v___x_1720_;
}
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_b_1709_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_as_1726_, lean_object* v_i_1727_, lean_object* v_stop_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
size_t v_i_boxed_1738_; size_t v_stop_boxed_1739_; lean_object* v_res_1740_; 
v_i_boxed_1738_ = lean_unbox_usize(v_i_1727_);
lean_dec(v_i_1727_);
v_stop_boxed_1739_ = lean_unbox_usize(v_stop_1728_);
lean_dec(v_stop_1728_);
v_res_1740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_1726_, v_i_boxed_1738_, v_stop_boxed_1739_, v_b_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v_as_1726_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_x_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(lean_object* v_t_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_root_1760_; lean_object* v_tail_1761_; lean_object* v___x_1762_; 
v_root_1760_ = lean_ctor_get(v_t_1751_, 0);
lean_inc_ref(v_root_1760_);
v_tail_1761_ = lean_ctor_get(v_t_1751_, 1);
lean_inc_ref(v_tail_1761_);
lean_dec_ref(v_t_1751_);
v___x_1762_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_1760_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1783_; 
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v___x_1762_, 0);
lean_dec(v_unused_1784_);
v___x_1764_ = v___x_1762_;
v_isShared_1765_ = v_isSharedCheck_1783_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v___x_1762_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1783_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = lean_array_get_size(v_tail_1761_);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_nat_dec_lt(v___x_1766_, v___x_1767_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_tail_1761_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1768_);
v___x_1771_ = v___x_1764_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1768_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_nat_dec_le(v___x_1767_, v___x_1767_);
if (v___x_1773_ == 0)
{
if (v___x_1769_ == 0)
{
lean_object* v___x_1775_; 
lean_dec_ref(v_tail_1761_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1768_);
v___x_1775_ = v___x_1764_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1768_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
else
{
size_t v___x_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
lean_del_object(v___x_1764_);
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = lean_usize_of_nat(v___x_1767_);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1761_, v___x_1777_, v___x_1778_, v___x_1768_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec_ref(v_tail_1761_);
return v___x_1779_;
}
}
else
{
size_t v___x_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
lean_del_object(v___x_1764_);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = lean_usize_of_nat(v___x_1767_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1761_, v___x_1780_, v___x_1781_, v___x_1768_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec_ref(v_tail_1761_);
return v___x_1782_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(lean_object* v_t_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1794_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(lean_object* v_x_1796_, size_t v_x_1797_, size_t v_x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
if (lean_obj_tag(v_x_1796_) == 0)
{
lean_object* v_cs_1807_; lean_object* v___x_1808_; size_t v___x_1809_; lean_object* v_j_1810_; lean_object* v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v_cs_1807_ = lean_ctor_get(v_x_1796_, 0);
lean_inc_ref(v_cs_1807_);
lean_dec_ref_known(v_x_1796_, 1);
v___x_1808_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
v___x_1809_ = lean_usize_shift_right(v_x_1797_, v_x_1798_);
v_j_1810_ = lean_usize_to_nat(v___x_1809_);
v___x_1811_ = lean_array_get_borrowed(v___x_1808_, v_cs_1807_, v_j_1810_);
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_shift_left(v___x_1812_, v_x_1798_);
v___x_1814_ = lean_usize_sub(v___x_1813_, v___x_1812_);
v___x_1815_ = lean_usize_land(v_x_1797_, v___x_1814_);
v___x_1816_ = ((size_t)5ULL);
v___x_1817_ = lean_usize_sub(v_x_1798_, v___x_1816_);
lean_inc(v___x_1811_);
v___x_1818_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_1811_, v___x_1815_, v___x_1817_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1840_; 
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; 
v_unused_1841_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1841_);
v___x_1820_ = v___x_1818_;
v_isShared_1821_ = v_isSharedCheck_1840_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1818_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1840_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = lean_nat_add(v_j_1810_, v___x_1822_);
lean_dec(v_j_1810_);
v___x_1824_ = lean_array_get_size(v_cs_1807_);
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_nat_dec_lt(v___x_1823_, v___x_1824_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1828_; 
lean_dec(v___x_1823_);
lean_dec_ref(v_cs_1807_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1825_);
v___x_1828_ = v___x_1820_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1825_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_nat_dec_le(v___x_1824_, v___x_1824_);
if (v___x_1830_ == 0)
{
if (v___x_1826_ == 0)
{
lean_object* v___x_1832_; 
lean_dec(v___x_1823_);
lean_dec_ref(v_cs_1807_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1825_);
v___x_1832_ = v___x_1820_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1825_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
else
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
lean_del_object(v___x_1820_);
v___x_1834_ = lean_usize_of_nat(v___x_1823_);
lean_dec(v___x_1823_);
v___x_1835_ = lean_usize_of_nat(v___x_1824_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1807_, v___x_1834_, v___x_1835_, v___x_1825_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v_cs_1807_);
return v___x_1836_;
}
}
else
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
lean_del_object(v___x_1820_);
v___x_1837_ = lean_usize_of_nat(v___x_1823_);
lean_dec(v___x_1823_);
v___x_1838_ = lean_usize_of_nat(v___x_1824_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_1807_, v___x_1837_, v___x_1838_, v___x_1825_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v_cs_1807_);
return v___x_1839_;
}
}
}
}
else
{
lean_dec(v_j_1810_);
lean_dec_ref(v_cs_1807_);
return v___x_1818_;
}
}
else
{
lean_object* v_vs_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1863_; 
v_vs_1842_ = lean_ctor_get(v_x_1796_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_x_1796_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1844_ = v_x_1796_;
v_isShared_1845_ = v_isSharedCheck_1863_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_vs_1842_);
lean_dec(v_x_1796_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1863_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1846_ = lean_usize_to_nat(v_x_1797_);
v___x_1847_ = lean_array_get_size(v_vs_1842_);
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_nat_dec_lt(v___x_1846_, v___x_1847_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1851_; 
lean_dec(v___x_1846_);
lean_dec_ref(v_vs_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1848_);
v___x_1851_ = v___x_1844_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1848_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_nat_dec_le(v___x_1847_, v___x_1847_);
if (v___x_1853_ == 0)
{
if (v___x_1849_ == 0)
{
lean_object* v___x_1855_; 
lean_dec(v___x_1846_);
lean_dec_ref(v_vs_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1848_);
v___x_1855_ = v___x_1844_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1848_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
else
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
lean_del_object(v___x_1844_);
v___x_1857_ = lean_usize_of_nat(v___x_1846_);
lean_dec(v___x_1846_);
v___x_1858_ = lean_usize_of_nat(v___x_1847_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1842_, v___x_1857_, v___x_1858_, v___x_1848_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v_vs_1842_);
return v___x_1859_;
}
}
else
{
size_t v___x_1860_; size_t v___x_1861_; lean_object* v___x_1862_; 
lean_del_object(v___x_1844_);
v___x_1860_ = lean_usize_of_nat(v___x_1846_);
lean_dec(v___x_1846_);
v___x_1861_ = lean_usize_of_nat(v___x_1847_);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_1842_, v___x_1860_, v___x_1861_, v___x_1848_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v_vs_1842_);
return v___x_1862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
size_t v_x_15412__boxed_1875_; size_t v_x_15413__boxed_1876_; lean_object* v_res_1877_; 
v_x_15412__boxed_1875_ = lean_unbox_usize(v_x_1865_);
lean_dec(v_x_1865_);
v_x_15413__boxed_1876_ = lean_unbox_usize(v_x_1866_);
lean_dec(v_x_1866_);
v_res_1877_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1864_, v_x_15412__boxed_1875_, v_x_15413__boxed_1876_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(lean_object* v_t_1878_, lean_object* v_start_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_nat_dec_eq(v_start_1879_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v_root_1890_; lean_object* v_tail_1891_; size_t v_shift_1892_; lean_object* v_tailOff_1893_; uint8_t v___x_1894_; 
v_root_1890_ = lean_ctor_get(v_t_1878_, 0);
lean_inc_ref(v_root_1890_);
v_tail_1891_ = lean_ctor_get(v_t_1878_, 1);
lean_inc_ref(v_tail_1891_);
v_shift_1892_ = lean_ctor_get_usize(v_t_1878_, 4);
v_tailOff_1893_ = lean_ctor_get(v_t_1878_, 3);
lean_inc(v_tailOff_1893_);
lean_dec_ref(v_t_1878_);
v___x_1894_ = lean_nat_dec_le(v_tailOff_1893_, v_start_1879_);
if (v___x_1894_ == 0)
{
size_t v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_tailOff_1893_);
v___x_1895_ = lean_usize_of_nat(v_start_1879_);
v___x_1896_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_1890_, v___x_1895_, v_shift_1892_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1916_; 
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v___x_1896_, 0);
lean_dec(v_unused_1917_);
v___x_1898_ = v___x_1896_;
v_isShared_1899_ = v_isSharedCheck_1916_;
goto v_resetjp_1897_;
}
else
{
lean_dec(v___x_1896_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1916_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1900_ = lean_array_get_size(v_tail_1891_);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_nat_dec_lt(v___x_1888_, v___x_1900_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1904_; 
lean_dec_ref(v_tail_1891_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1901_);
v___x_1904_ = v___x_1898_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1901_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_nat_dec_le(v___x_1900_, v___x_1900_);
if (v___x_1906_ == 0)
{
if (v___x_1902_ == 0)
{
lean_object* v___x_1908_; 
lean_dec_ref(v_tail_1891_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1901_);
v___x_1908_ = v___x_1898_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1901_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
else
{
size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
lean_del_object(v___x_1898_);
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = lean_usize_of_nat(v___x_1900_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1891_, v___x_1910_, v___x_1911_, v___x_1901_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec_ref(v_tail_1891_);
return v___x_1912_;
}
}
else
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
lean_del_object(v___x_1898_);
v___x_1913_ = ((size_t)0ULL);
v___x_1914_ = lean_usize_of_nat(v___x_1900_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1891_, v___x_1913_, v___x_1914_, v___x_1901_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec_ref(v_tail_1891_);
return v___x_1915_;
}
}
}
}
else
{
lean_dec_ref(v_tail_1891_);
return v___x_1896_;
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
lean_dec_ref(v_root_1890_);
v___x_1918_ = lean_nat_sub(v_start_1879_, v_tailOff_1893_);
lean_dec(v_tailOff_1893_);
v___x_1919_ = lean_array_get_size(v_tail_1891_);
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_nat_dec_lt(v___x_1918_, v___x_1919_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; 
lean_dec(v___x_1918_);
lean_dec_ref(v_tail_1891_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
return v___x_1922_;
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = lean_nat_dec_le(v___x_1919_, v___x_1919_);
if (v___x_1923_ == 0)
{
if (v___x_1921_ == 0)
{
lean_object* v___x_1924_; 
lean_dec(v___x_1918_);
lean_dec_ref(v_tail_1891_);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1920_);
return v___x_1924_;
}
else
{
size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_usize_of_nat(v___x_1918_);
lean_dec(v___x_1918_);
v___x_1926_ = lean_usize_of_nat(v___x_1919_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1891_, v___x_1925_, v___x_1926_, v___x_1920_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec_ref(v_tail_1891_);
return v___x_1927_;
}
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_usize_of_nat(v___x_1918_);
lean_dec(v___x_1918_);
v___x_1929_ = lean_usize_of_nat(v___x_1919_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_1891_, v___x_1928_, v___x_1929_, v___x_1920_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec_ref(v_tail_1891_);
return v___x_1930_;
}
}
}
}
else
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_1878_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(lean_object* v_t_1932_, lean_object* v_start_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_1932_, v_start_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v_start_1933_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(lean_object* v_lctx_1943_, lean_object* v_start_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_decls_1953_; lean_object* v___x_1954_; 
v_decls_1953_ = lean_ctor_get(v_lctx_1943_, 1);
lean_inc_ref(v_decls_1953_);
lean_dec_ref(v_lctx_1943_);
v___x_1954_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_1953_, v_start_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(lean_object* v_lctx_1955_, lean_object* v_start_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1955_, v_start_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v_start_1956_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap(lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_lctx_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_lctx_1974_ = lean_ctor_get(v_a_1969_, 2);
v___x_1975_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1974_);
v___x_1976_ = l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(v_lctx_1974_, v___x_1975_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_initializeValueMap___boxed(lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
return v_res_1985_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ExtractLets_containsLet(lean_object* v_e_1987_){
_start:
{
lean_object* v___f_1988_; lean_object* v___x_1989_; 
v___f_1988_ = ((lean_object*)(l_Lean_Meta_ExtractLets_containsLet___closed__0));
v___x_1989_ = lean_find_expr(v___f_1988_, v_e_1987_);
if (lean_obj_tag(v___x_1989_) == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = 0;
return v___x_1990_;
}
else
{
uint8_t v___x_1991_; 
lean_dec_ref_known(v___x_1989_, 1);
v___x_1991_ = 1;
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_containsLet___boxed(lean_object* v_e_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Lean_Meta_ExtractLets_containsLet(v_e_1992_);
lean_dec_ref(v_e_1992_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(lean_object* v_k_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v_b_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
v___x_2005_ = lean_apply_9(v_k_1995_, v_b_1999_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, lean_box(0));
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v_b_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_2017_, uint8_t v_bi_2018_, lean_object* v_type_2019_, lean_object* v_k_2020_, uint8_t v_kind_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___f_2030_; lean_object* v___x_2031_; 
lean_inc(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2030_, 0, v_k_2020_);
lean_closure_set(v___f_2030_, 1, v___y_2022_);
lean_closure_set(v___f_2030_, 2, v___y_2023_);
lean_closure_set(v___f_2030_, 3, v___y_2024_);
v___x_2031_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2017_, v_bi_2018_, v_type_2019_, v___f_2030_, v_kind_2021_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2031_) == 0)
{
return v___x_2031_;
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(lean_object* v_name_2040_, lean_object* v_bi_2041_, lean_object* v_type_2042_, lean_object* v_k_2043_, lean_object* v_kind_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
uint8_t v_bi_boxed_2053_; uint8_t v_kind_boxed_2054_; lean_object* v_res_2055_; 
v_bi_boxed_2053_ = lean_unbox(v_bi_2041_);
v_kind_boxed_2054_ = lean_unbox(v_kind_2044_);
v_res_2055_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_2040_, v_bi_boxed_2053_, v_type_2042_, v_k_2043_, v_kind_boxed_2054_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(lean_object* v_00_u03b1_2056_, lean_object* v_name_2057_, uint8_t v_bi_2058_, lean_object* v_type_2059_, lean_object* v_k_2060_, uint8_t v_kind_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_2057_, v_bi_2058_, v_type_2059_, v_k_2060_, v_kind_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(lean_object* v_00_u03b1_2071_, lean_object* v_name_2072_, lean_object* v_bi_2073_, lean_object* v_type_2074_, lean_object* v_k_2075_, lean_object* v_kind_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v_bi_boxed_2085_; uint8_t v_kind_boxed_2086_; lean_object* v_res_2087_; 
v_bi_boxed_2085_ = lean_unbox(v_bi_2073_);
v_kind_boxed_2086_ = lean_unbox(v_kind_2076_);
v_res_2087_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_2071_, v_name_2072_, v_bi_boxed_2085_, v_type_2074_, v_k_2075_, v_kind_boxed_2086_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_m_2088_, lean_object* v_query_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v_zero_2093_; uint8_t v_isZero_2094_; 
v_zero_2093_ = lean_unsigned_to_nat(0u);
v_isZero_2094_ = lean_nat_dec_eq(v_x_2091_, v_zero_2093_);
if (v_isZero_2094_ == 1)
{
lean_dec(v_x_2092_);
lean_dec(v_x_2091_);
if (lean_obj_tag(v_x_2090_) == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_box(2);
return v___x_2095_;
}
else
{
lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_val_2096_ = lean_ctor_get(v_x_2090_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_2090_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v_x_2090_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_dec(v_x_2090_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_val_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_keyArray_2104_; lean_object* v_valueArray_2105_; lean_object* v___x_2106_; uint8_t v_isSome_2107_; 
v_keyArray_2104_ = lean_ctor_get(v_m_2088_, 1);
v_valueArray_2105_ = lean_ctor_get(v_m_2088_, 2);
v___x_2106_ = lean_array_fget_borrowed(v_keyArray_2104_, v_x_2092_);
v_isSome_2107_ = lean_noption_is_some(v___x_2106_);
if (v_isSome_2107_ == 0)
{
lean_dec(v_x_2091_);
if (lean_obj_tag(v_x_2090_) == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_x_2092_);
return v___x_2108_;
}
else
{
lean_object* v_val_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_x_2092_);
v_val_2109_ = lean_ctor_get(v_x_2090_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_x_2090_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v_x_2090_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_val_2109_);
lean_dec(v_x_2090_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_val_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_one_2117_; lean_object* v_n_2118_; lean_object* v___y_2120_; 
v_one_2117_ = lean_unsigned_to_nat(1u);
v_n_2118_ = lean_nat_sub(v_x_2091_, v_one_2117_);
lean_dec(v_x_2091_);
if (v_isSome_2107_ == 0)
{
goto v___jp_2126_;
}
else
{
lean_object* v___x_2134_; uint8_t v_isSome_2135_; 
v___x_2134_ = lean_array_fget_borrowed(v_valueArray_2105_, v_x_2092_);
v_isSome_2135_ = lean_noption_is_some(v___x_2134_);
if (v_isSome_2135_ == 0)
{
goto v___jp_2126_;
}
else
{
lean_object* v_val_2136_; lean_object* v_fst_2137_; lean_object* v_snd_2138_; lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v_val_2141_; uint8_t v___y_2143_; uint8_t v___x_2146_; 
lean_inc(v___x_2106_);
v_val_2136_ = lean_noption_get(v___x_2106_);
v_fst_2137_ = lean_ctor_get(v_val_2136_, 0);
lean_inc(v_fst_2137_);
v_snd_2138_ = lean_ctor_get(v_val_2136_, 1);
lean_inc(v_snd_2138_);
v_fst_2139_ = lean_ctor_get(v_query_2089_, 0);
v_snd_2140_ = lean_ctor_get(v_query_2089_, 1);
lean_inc(v___x_2134_);
v_val_2141_ = lean_noption_get(v___x_2134_);
v___x_2146_ = lean_unbox(v_fst_2137_);
lean_dec(v_fst_2137_);
if (v___x_2146_ == 0)
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_unbox(v_fst_2139_);
if (v___x_2147_ == 0)
{
v___y_2143_ = v_isSome_2135_;
goto v___jp_2142_;
}
else
{
lean_dec(v_val_2141_);
lean_dec(v_snd_2138_);
lean_dec(v_val_2136_);
goto v___jp_2128_;
}
}
else
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_unbox(v_fst_2139_);
v___y_2143_ = v___x_2148_;
goto v___jp_2142_;
}
v___jp_2142_:
{
if (v___y_2143_ == 0)
{
lean_dec(v_val_2141_);
lean_dec(v_snd_2138_);
lean_dec(v_val_2136_);
goto v___jp_2128_;
}
else
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Lean_ExprStructEq_beq(v_snd_2138_, v_snd_2140_);
lean_dec(v_snd_2138_);
if (v___x_2144_ == 0)
{
lean_dec(v_val_2141_);
lean_dec(v_val_2136_);
goto v___jp_2128_;
}
else
{
lean_object* v___x_2145_; 
lean_dec(v_n_2118_);
lean_dec(v_x_2090_);
v___x_2145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2145_, 0, v_x_2092_);
lean_ctor_set(v___x_2145_, 1, v_val_2136_);
lean_ctor_set(v___x_2145_, 2, v_val_2141_);
return v___x_2145_;
}
}
}
}
}
v___jp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2121_ = lean_array_get_size(v_keyArray_2104_);
v___x_2122_ = lean_nat_add(v_x_2092_, v_one_2117_);
lean_dec(v_x_2092_);
v___x_2123_ = lean_nat_dec_lt(v___x_2122_, v___x_2121_);
if (v___x_2123_ == 0)
{
lean_dec(v___x_2122_);
v_x_2090_ = v___y_2120_;
v_x_2091_ = v_n_2118_;
v_x_2092_ = v_zero_2093_;
goto _start;
}
else
{
v_x_2090_ = v___y_2120_;
v_x_2091_ = v_n_2118_;
v_x_2092_ = v___x_2122_;
goto _start;
}
}
v___jp_2126_:
{
if (lean_obj_tag(v_x_2090_) == 0)
{
lean_object* v___x_2127_; 
lean_inc(v_x_2092_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v_x_2092_);
v___y_2120_ = v___x_2127_;
goto v___jp_2119_;
}
else
{
v___y_2120_ = v_x_2090_;
goto v___jp_2119_;
}
}
v___jp_2128_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2129_ = lean_array_get_size(v_keyArray_2104_);
v___x_2130_ = lean_nat_add(v_x_2092_, v_one_2117_);
lean_dec(v_x_2092_);
v___x_2131_ = lean_nat_dec_lt(v___x_2130_, v___x_2129_);
if (v___x_2131_ == 0)
{
lean_dec(v___x_2130_);
v_x_2091_ = v_n_2118_;
v_x_2092_ = v_zero_2093_;
goto _start;
}
else
{
v_x_2091_ = v_n_2118_;
v_x_2092_ = v___x_2130_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_m_2149_, lean_object* v_query_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_m_2149_, v_query_2150_, v_x_2151_, v_x_2152_, v_x_2153_);
lean_dec_ref(v_query_2150_);
lean_dec_ref(v_m_2149_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2155_, lean_object* v_query_2156_){
_start:
{
lean_object* v_keyArray_2157_; lean_object* v_fst_2158_; lean_object* v_snd_2159_; lean_object* v___x_2160_; uint64_t v___y_2162_; uint8_t v___x_2179_; 
v_keyArray_2157_ = lean_ctor_get(v_m_2155_, 1);
v_fst_2158_ = lean_ctor_get(v_query_2156_, 0);
v_snd_2159_ = lean_ctor_get(v_query_2156_, 1);
v___x_2160_ = lean_array_get_size(v_keyArray_2157_);
v___x_2179_ = lean_unbox(v_fst_2158_);
if (v___x_2179_ == 0)
{
uint64_t v___x_2180_; 
v___x_2180_ = 13ULL;
v___y_2162_ = v___x_2180_;
goto v___jp_2161_;
}
else
{
uint64_t v___x_2181_; 
v___x_2181_ = 11ULL;
v___y_2162_ = v___x_2181_;
goto v___jp_2161_;
}
v___jp_2161_:
{
uint64_t v___x_2163_; uint64_t v___x_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; uint64_t v_fold_2167_; uint64_t v___x_2168_; uint64_t v___x_2169_; uint64_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2163_ = l_Lean_ExprStructEq_hash(v_snd_2159_);
v___x_2164_ = lean_uint64_mix_hash(v___y_2162_, v___x_2163_);
v___x_2165_ = 32ULL;
v___x_2166_ = lean_uint64_shift_right(v___x_2164_, v___x_2165_);
v_fold_2167_ = lean_uint64_xor(v___x_2164_, v___x_2166_);
v___x_2168_ = 16ULL;
v___x_2169_ = lean_uint64_shift_right(v_fold_2167_, v___x_2168_);
v___x_2170_ = lean_uint64_xor(v_fold_2167_, v___x_2169_);
v___x_2171_ = lean_uint64_to_usize(v___x_2170_);
v___x_2172_ = lean_usize_of_nat(v___x_2160_);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_sub(v___x_2172_, v___x_2173_);
v___x_2175_ = lean_usize_land(v___x_2171_, v___x_2174_);
v___x_2176_ = lean_usize_to_nat(v___x_2175_);
v___x_2177_ = lean_box(0);
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_m_2155_, v_query_2156_, v___x_2177_, v___x_2160_, v___x_2176_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg___boxed(lean_object* v_m_2182_, lean_object* v_query_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_2182_, v_query_2183_);
lean_dec_ref(v_query_2183_);
lean_dec_ref(v_m_2182_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___redArg(lean_object* v_m_2185_, lean_object* v_query_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_2185_, v_query_2186_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_index_2188_; lean_object* v_key_2189_; lean_object* v_value_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_index_2188_ = lean_ctor_get(v___x_2187_, 0);
v_key_2189_ = lean_ctor_get(v___x_2187_, 1);
v_value_2190_ = lean_ctor_get(v___x_2187_, 2);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2187_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_value_2190_);
lean_inc(v_key_2189_);
lean_inc(v_index_2188_);
lean_dec(v___x_2187_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_index_2188_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_key_2189_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_value_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
else
{
lean_object* v___x_2198_; 
lean_dec(v___x_2187_);
v___x_2198_ = lean_box(1);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___redArg___boxed(lean_object* v_m_2199_, lean_object* v_query_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___redArg(v_m_2199_, v_query_2200_);
lean_dec_ref(v_query_2200_);
lean_dec_ref(v_m_2199_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___redArg(lean_object* v_m_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___redArg(v_m_2202_, v_a_2203_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_value_2205_; lean_object* v___x_2206_; 
v_value_2205_ = lean_ctor_get(v___x_2204_, 2);
lean_inc(v_value_2205_);
lean_dec_ref_known(v___x_2204_, 3);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_value_2205_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_box(0);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___redArg___boxed(lean_object* v_m_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___redArg(v_m_2208_, v_a_2209_);
lean_dec_ref(v_a_2209_);
lean_dec_ref(v_m_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___redArg(lean_object* v_b_2211_, lean_object* v_acc_2212_, lean_object* v_i_2213_){
_start:
{
lean_object* v___y_2215_; lean_object* v_keyArray_2223_; lean_object* v_valueArray_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v_keyArray_2223_ = lean_ctor_get(v_b_2211_, 1);
v_valueArray_2224_ = lean_ctor_get(v_b_2211_, 2);
v___x_2225_ = lean_array_get_size(v_keyArray_2223_);
v___x_2226_ = lean_nat_dec_lt(v_i_2213_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_dec(v_i_2213_);
return v_acc_2212_;
}
else
{
lean_object* v___x_2227_; uint8_t v_isSome_2228_; 
v___x_2227_ = lean_array_fget_borrowed(v_keyArray_2223_, v_i_2213_);
v_isSome_2228_ = lean_noption_is_some(v___x_2227_);
if (v_isSome_2228_ == 0)
{
goto v___jp_2219_;
}
else
{
lean_object* v___x_2229_; uint8_t v_isSome_2230_; 
v___x_2229_ = lean_array_fget_borrowed(v_valueArray_2224_, v_i_2213_);
v_isSome_2230_ = lean_noption_is_some(v___x_2229_);
if (v_isSome_2230_ == 0)
{
goto v___jp_2219_;
}
else
{
lean_object* v_val_2231_; lean_object* v_val_2232_; lean_object* v_i_2234_; lean_object* v___x_2239_; 
lean_inc(v___x_2227_);
v_val_2231_ = lean_noption_get(v___x_2227_);
lean_inc(v___x_2229_);
v_val_2232_ = lean_noption_get(v___x_2229_);
v___x_2239_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_acc_2212_, v_val_2231_);
switch(lean_obj_tag(v___x_2239_))
{
case 0:
{
lean_object* v_index_2240_; lean_object* v_size_2241_; lean_object* v___x_2242_; 
v_index_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_index_2240_);
lean_dec_ref_known(v___x_2239_, 3);
v_size_2241_ = lean_ctor_get(v_acc_2212_, 0);
lean_inc(v_size_2241_);
v___x_2242_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2212_, v_size_2241_, v_index_2240_, v_val_2231_, v_val_2232_);
lean_dec(v_index_2240_);
v___y_2215_ = v___x_2242_;
goto v___jp_2214_;
}
case 1:
{
lean_object* v_index_2243_; 
v_index_2243_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_index_2243_);
lean_dec_ref_known(v___x_2239_, 1);
v_i_2234_ = v_index_2243_;
goto v___jp_2233_;
}
default: 
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2212_, v___x_2244_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_index_2246_; 
v_index_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_index_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v_i_2234_ = v_index_2246_;
goto v___jp_2233_;
}
else
{
lean_dec(v_val_2232_);
lean_dec(v_val_2231_);
v___y_2215_ = v_acc_2212_;
goto v___jp_2214_;
}
}
}
v___jp_2233_:
{
lean_object* v_size_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_size_2235_ = lean_ctor_get(v_acc_2212_, 0);
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_add(v_size_2235_, v___x_2236_);
v___x_2238_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2212_, v___x_2237_, v_i_2234_, v_val_2231_, v_val_2232_);
lean_dec(v_i_2234_);
v___y_2215_ = v___x_2238_;
goto v___jp_2214_;
}
}
}
}
v___jp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_add(v_i_2213_, v___x_2216_);
lean_dec(v_i_2213_);
v_acc_2212_ = v___y_2215_;
v_i_2213_ = v___x_2217_;
goto _start;
}
v___jp_2219_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_unsigned_to_nat(1u);
v___x_2221_ = lean_nat_add(v_i_2213_, v___x_2220_);
lean_dec(v_i_2213_);
v_i_2213_ = v___x_2221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___redArg___boxed(lean_object* v_b_2247_, lean_object* v_acc_2248_, lean_object* v_i_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___redArg(v_b_2247_, v_acc_2248_, v_i_2249_);
lean_dec_ref(v_b_2247_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___redArg(lean_object* v_init_2251_, lean_object* v_b_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___redArg(v_b_2252_, v_init_2251_, v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___redArg___boxed(lean_object* v_init_2255_, lean_object* v_b_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___redArg(v_init_2255_, v_b_2256_);
lean_dec_ref(v_b_2256_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2258_){
_start:
{
lean_object* v_keyArray_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_cellCount_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_target_2266_; lean_object* v___x_2267_; 
v_keyArray_2259_ = lean_ctor_get(v_m_2258_, 1);
v___x_2260_ = lean_array_get_size(v_keyArray_2259_);
v___x_2261_ = lean_unsigned_to_nat(2u);
v_cellCount_2262_ = lean_nat_mul(v___x_2260_, v___x_2261_);
v___x_2263_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2262_);
v___x_2264_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2262_);
v___x_2265_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2262_);
v_target_2266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2266_, 0, v___x_2263_);
lean_ctor_set(v_target_2266_, 1, v___x_2264_);
lean_ctor_set(v_target_2266_, 2, v___x_2265_);
v___x_2267_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___redArg(v_target_2266_, v_m_2258_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2268_);
lean_dec_ref(v_m_2268_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderName_2270_, uint8_t v_binderInfo_2271_, lean_object* v_e_2272_, lean_object* v_binderType_2273_, lean_object* v_body_2274_, lean_object* v_t_2275_, lean_object* v_b_2276_){
_start:
{
uint8_t v___y_2278_; size_t v___x_2282_; size_t v___x_2283_; uint8_t v___x_2284_; 
v___x_2282_ = lean_ptr_addr(v_binderType_2273_);
v___x_2283_ = lean_ptr_addr(v_t_2275_);
v___x_2284_ = lean_usize_dec_eq(v___x_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
v___y_2278_ = v___x_2284_;
goto v___jp_2277_;
}
else
{
size_t v___x_2285_; size_t v___x_2286_; uint8_t v___x_2287_; 
v___x_2285_ = lean_ptr_addr(v_body_2274_);
v___x_2286_ = lean_ptr_addr(v_b_2276_);
v___x_2287_ = lean_usize_dec_eq(v___x_2285_, v___x_2286_);
v___y_2278_ = v___x_2287_;
goto v___jp_2277_;
}
v___jp_2277_:
{
if (v___y_2278_ == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Expr_lam___override(v_binderName_2270_, v_t_2275_, v_b_2276_, v_binderInfo_2271_);
return v___x_2279_;
}
else
{
uint8_t v___x_2280_; 
v___x_2280_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2271_, v_binderInfo_2271_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Expr_lam___override(v_binderName_2270_, v_t_2275_, v_b_2276_, v_binderInfo_2271_);
return v___x_2281_;
}
else
{
lean_dec_ref(v_b_2276_);
lean_dec_ref(v_t_2275_);
lean_dec(v_binderName_2270_);
lean_inc_ref(v_e_2272_);
return v_e_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderName_2288_, lean_object* v_binderInfo_2289_, lean_object* v_e_2290_, lean_object* v_binderType_2291_, lean_object* v_body_2292_, lean_object* v_t_2293_, lean_object* v_b_2294_){
_start:
{
uint8_t v_binderInfo_56742__boxed_2295_; lean_object* v_res_2296_; 
v_binderInfo_56742__boxed_2295_ = lean_unbox(v_binderInfo_2289_);
v_res_2296_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderName_2288_, v_binderInfo_56742__boxed_2295_, v_e_2290_, v_binderType_2291_, v_body_2292_, v_t_2293_, v_b_2294_);
lean_dec_ref(v_body_2292_);
lean_dec_ref(v_binderType_2291_);
lean_dec_ref(v_e_2290_);
return v_res_2296_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___lam__0(uint8_t v___y_2297_, uint8_t v___y_2298_){
_start:
{
if (v___y_2297_ == 0)
{
if (v___y_2298_ == 0)
{
uint8_t v___x_2299_; 
v___x_2299_ = 1;
return v___x_2299_;
}
else
{
return v___y_2297_;
}
}
else
{
return v___y_2298_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___lam__0___boxed(lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v___y_56775__boxed_2302_; uint8_t v___y_56776__boxed_2303_; uint8_t v_res_2304_; lean_object* v_r_2305_; 
v___y_56775__boxed_2302_ = lean_unbox(v___y_2300_);
v___y_56776__boxed_2303_ = lean_unbox(v___y_2301_);
v_res_2304_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___lam__0(v___y_56775__boxed_2302_, v___y_56776__boxed_2303_);
v_r_2305_ = lean_box(v_res_2304_);
return v_r_2305_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_instMonadEIO(lean_box(0));
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5(lean_object* v_msg_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v_toApplicative_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2397_; 
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__0);
v___x_2325_ = l_StateRefT_x27_instMonad___redArg(v___x_2324_);
v_toApplicative_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v___x_2325_, 1);
lean_dec(v_unused_2398_);
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2397_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_toApplicative_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2397_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_toFunctor_2330_; lean_object* v_toSeq_2331_; lean_object* v_toSeqLeft_2332_; lean_object* v_toSeqRight_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2395_; 
v_toFunctor_2330_ = lean_ctor_get(v_toApplicative_2326_, 0);
v_toSeq_2331_ = lean_ctor_get(v_toApplicative_2326_, 2);
v_toSeqLeft_2332_ = lean_ctor_get(v_toApplicative_2326_, 3);
v_toSeqRight_2333_ = lean_ctor_get(v_toApplicative_2326_, 4);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_toApplicative_2326_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v_toApplicative_2326_, 1);
lean_dec(v_unused_2396_);
v___x_2335_ = v_toApplicative_2326_;
v_isShared_2336_ = v_isSharedCheck_2395_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_toSeqRight_2333_);
lean_inc(v_toSeqLeft_2332_);
lean_inc(v_toSeq_2331_);
lean_inc(v_toFunctor_2330_);
lean_dec(v_toApplicative_2326_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2395_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___f_2337_; lean_object* v___f_2338_; lean_object* v___f_2339_; lean_object* v___f_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; lean_object* v___f_2343_; lean_object* v___f_2344_; lean_object* v___x_2346_; 
v___f_2337_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__1));
v___f_2338_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__2));
lean_inc_ref(v_toFunctor_2330_);
v___f_2339_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2339_, 0, v_toFunctor_2330_);
v___f_2340_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2340_, 0, v_toFunctor_2330_);
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___f_2339_);
lean_ctor_set(v___x_2341_, 1, v___f_2340_);
v___f_2342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2342_, 0, v_toSeqRight_2333_);
v___f_2343_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2343_, 0, v_toSeqLeft_2332_);
v___f_2344_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2344_, 0, v_toSeq_2331_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 4, v___f_2342_);
lean_ctor_set(v___x_2335_, 3, v___f_2343_);
lean_ctor_set(v___x_2335_, 2, v___f_2344_);
lean_ctor_set(v___x_2335_, 1, v___f_2337_);
lean_ctor_set(v___x_2335_, 0, v___x_2341_);
v___x_2346_ = v___x_2335_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___f_2337_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v___f_2344_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v___f_2343_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v___f_2342_);
v___x_2346_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___f_2338_);
lean_ctor_set(v___x_2328_, 0, v___x_2346_);
v___x_2348_ = v___x_2328_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___f_2338_);
v___x_2348_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v_toApplicative_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2391_; 
v___x_2349_ = l_StateRefT_x27_instMonad___redArg(v___x_2348_);
v_toApplicative_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; 
v_unused_2392_ = lean_ctor_get(v___x_2349_, 1);
lean_dec(v_unused_2392_);
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2391_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_toApplicative_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2391_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_toFunctor_2354_; lean_object* v_toSeq_2355_; lean_object* v_toSeqLeft_2356_; lean_object* v_toSeqRight_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2389_; 
v_toFunctor_2354_ = lean_ctor_get(v_toApplicative_2350_, 0);
v_toSeq_2355_ = lean_ctor_get(v_toApplicative_2350_, 2);
v_toSeqLeft_2356_ = lean_ctor_get(v_toApplicative_2350_, 3);
v_toSeqRight_2357_ = lean_ctor_get(v_toApplicative_2350_, 4);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_toApplicative_2350_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v_toApplicative_2350_, 1);
lean_dec(v_unused_2390_);
v___x_2359_ = v_toApplicative_2350_;
v_isShared_2360_ = v_isSharedCheck_2389_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_toSeqRight_2357_);
lean_inc(v_toSeqLeft_2356_);
lean_inc(v_toSeq_2355_);
lean_inc(v_toFunctor_2354_);
lean_dec(v_toApplicative_2350_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2389_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___f_2361_; lean_object* v___f_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___f_2367_; lean_object* v___f_2368_; lean_object* v___f_2369_; lean_object* v___f_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___f_2375_; lean_object* v___x_2377_; 
v___f_2361_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___lam__0___boxed), 2, 0);
v___f_2362_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2362_, 0, v___f_2361_);
v___x_2363_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__3));
v___f_2364_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2364_, 0, v___f_2362_);
lean_closure_set(v___f_2364_, 1, v___x_2363_);
v___f_2365_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__4));
v___x_2366_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__5));
v___f_2367_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2367_, 0, v___f_2365_);
lean_closure_set(v___f_2367_, 1, v___x_2366_);
v___f_2368_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__6));
v___f_2369_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___closed__7));
lean_inc_ref(v_toFunctor_2354_);
v___f_2370_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2370_, 0, v_toFunctor_2354_);
v___f_2371_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2371_, 0, v_toFunctor_2354_);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___f_2370_);
lean_ctor_set(v___x_2372_, 1, v___f_2371_);
v___f_2373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2373_, 0, v_toSeqRight_2357_);
v___f_2374_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2374_, 0, v_toSeqLeft_2356_);
v___f_2375_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2375_, 0, v_toSeq_2355_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 4, v___f_2373_);
lean_ctor_set(v___x_2359_, 3, v___f_2374_);
lean_ctor_set(v___x_2359_, 2, v___f_2375_);
lean_ctor_set(v___x_2359_, 1, v___f_2368_);
lean_ctor_set(v___x_2359_, 0, v___x_2372_);
v___x_2377_ = v___x_2359_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___f_2368_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v___f_2375_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v___f_2374_);
lean_ctor_set(v_reuseFailAlloc_2388_, 4, v___f_2373_);
v___x_2377_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 1, v___f_2369_);
lean_ctor_set(v___x_2352_, 0, v___x_2377_);
v___x_2379_ = v___x_2352_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v___f_2369_);
v___x_2379_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___x_53506__overap_2385_; lean_object* v___x_2386_; 
v___x_2380_ = l_StateRefT_x27_instMonad___redArg(v___x_2379_);
v___x_2381_ = l_Lean_MonadCacheT_instMonad___redArg(v___x_2323_, v___f_2364_, v___f_2367_, v___x_2380_);
v___x_2382_ = l_Lean_instInhabitedExpr;
v___x_2383_ = l_instInhabitedOfMonad___redArg(v___x_2381_, v___x_2382_);
v___f_2384_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2384_, 0, v___x_2383_);
v___x_53506__overap_2385_ = lean_panic_fn_borrowed(v___f_2384_, v_msg_2314_);
lean_dec_ref(v___f_2384_);
lean_inc(v___y_2321_);
lean_inc_ref(v___y_2320_);
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v___y_2317_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
v___x_2386_ = lean_apply_8(v___x_53506__overap_2385_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, lean_box(0));
return v___x_2386_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5___boxed(lean_object* v_msg_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5(v_msg_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderName_2409_, uint8_t v_binderInfo_2410_, lean_object* v_e_2411_, lean_object* v_binderType_2412_, lean_object* v_body_2413_, lean_object* v_t_2414_, lean_object* v_b_2415_){
_start:
{
uint8_t v___y_2417_; size_t v___x_2421_; size_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2421_ = lean_ptr_addr(v_binderType_2412_);
v___x_2422_ = lean_ptr_addr(v_t_2414_);
v___x_2423_ = lean_usize_dec_eq(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
v___y_2417_ = v___x_2423_;
goto v___jp_2416_;
}
else
{
size_t v___x_2424_; size_t v___x_2425_; uint8_t v___x_2426_; 
v___x_2424_ = lean_ptr_addr(v_body_2413_);
v___x_2425_ = lean_ptr_addr(v_b_2415_);
v___x_2426_ = lean_usize_dec_eq(v___x_2424_, v___x_2425_);
v___y_2417_ = v___x_2426_;
goto v___jp_2416_;
}
v___jp_2416_:
{
if (v___y_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Expr_forallE___override(v_binderName_2409_, v_t_2414_, v_b_2415_, v_binderInfo_2410_);
return v___x_2418_;
}
else
{
uint8_t v___x_2419_; 
v___x_2419_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2410_, v_binderInfo_2410_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Expr_forallE___override(v_binderName_2409_, v_t_2414_, v_b_2415_, v_binderInfo_2410_);
return v___x_2420_;
}
else
{
lean_dec_ref(v_b_2415_);
lean_dec_ref(v_t_2414_);
lean_dec(v_binderName_2409_);
lean_inc_ref(v_e_2411_);
return v_e_2411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderName_2427_, lean_object* v_binderInfo_2428_, lean_object* v_e_2429_, lean_object* v_binderType_2430_, lean_object* v_body_2431_, lean_object* v_t_2432_, lean_object* v_b_2433_){
_start:
{
uint8_t v_binderInfo_56962__boxed_2434_; lean_object* v_res_2435_; 
v_binderInfo_56962__boxed_2434_ = lean_unbox(v_binderInfo_2428_);
v_res_2435_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderName_2427_, v_binderInfo_56962__boxed_2434_, v_e_2429_, v_binderType_2430_, v_body_2431_, v_t_2432_, v_b_2433_);
lean_dec_ref(v_body_2431_);
lean_dec_ref(v_binderType_2430_);
lean_dec_ref(v_e_2429_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_name_2436_, lean_object* v_type_2437_, lean_object* v_val_2438_, lean_object* v_k_2439_, uint8_t v_nondep_2440_, uint8_t v_kind_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___f_2450_; lean_object* v___x_2451_; 
lean_inc(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2450_, 0, v_k_2439_);
lean_closure_set(v___f_2450_, 1, v___y_2442_);
lean_closure_set(v___f_2450_, 2, v___y_2443_);
lean_closure_set(v___f_2450_, 3, v___y_2444_);
v___x_2451_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2436_, v_type_2437_, v_val_2438_, v___f_2450_, v_nondep_2440_, v_kind_2441_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2451_) == 0)
{
return v___x_2451_;
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_name_2460_, lean_object* v_type_2461_, lean_object* v_val_2462_, lean_object* v_k_2463_, lean_object* v_nondep_2464_, lean_object* v_kind_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
uint8_t v_nondep_boxed_2474_; uint8_t v_kind_boxed_2475_; lean_object* v_res_2476_; 
v_nondep_boxed_2474_ = lean_unbox(v_nondep_2464_);
v_kind_boxed_2475_ = lean_unbox(v_kind_2465_);
v_res_2476_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_name_2460_, v_type_2461_, v_val_2462_, v_k_2463_, v_nondep_boxed_2474_, v_kind_boxed_2475_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_msg_2477_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = l_Lean_instInhabitedExpr;
v___x_2479_ = lean_panic_fn_borrowed(v___x_2478_, v_msg_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___redArg(lean_object* v_m_2480_, lean_object* v_query_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_m_2480_, v_query_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_index_2483_; lean_object* v_key_2484_; lean_object* v_value_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
v_index_2483_ = lean_ctor_get(v___x_2482_, 0);
v_key_2484_ = lean_ctor_get(v___x_2482_, 1);
v_value_2485_ = lean_ctor_get(v___x_2482_, 2);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2482_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_value_2485_);
lean_inc(v_key_2484_);
lean_inc(v_index_2483_);
lean_dec(v___x_2482_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_index_2483_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_key_2484_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_value_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
else
{
lean_object* v___x_2493_; 
lean_dec(v___x_2482_);
v___x_2493_ = lean_box(1);
return v___x_2493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___redArg___boxed(lean_object* v_m_2494_, lean_object* v_query_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___redArg(v_m_2494_, v_query_2495_);
lean_dec_ref(v_query_2495_);
lean_dec_ref(v_m_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___redArg(lean_object* v_m_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___redArg(v_m_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_value_2500_; lean_object* v___x_2501_; 
v_value_2500_ = lean_ctor_get(v___x_2499_, 2);
lean_inc(v_value_2500_);
lean_dec_ref_known(v___x_2499_, 3);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_value_2500_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_box(0);
return v___x_2502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___redArg___boxed(lean_object* v_m_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___redArg(v_m_2503_, v_a_2504_);
lean_dec_ref(v_a_2504_);
lean_dec_ref(v_m_2503_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_2506_, lean_object* v_e_2507_, lean_object* v___f_2508_, lean_object* v_____r_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
if (v_types_2506_ == 0)
{
lean_object* v___x_2518_; 
lean_inc_ref(v_e_2507_);
v___x_2518_ = l_Lean_Meta_isType(v_e_2507_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2529_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2529_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2529_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_unbox(v_a_2519_);
lean_dec(v_a_2519_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_del_object(v___x_2521_);
lean_dec_ref(v_e_2507_);
v___x_2524_ = lean_box(0);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
v___x_2525_ = lean_apply_9(v___f_2508_, v___x_2524_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
return v___x_2525_;
}
else
{
lean_object* v___x_2527_; 
lean_dec_ref(v___f_2508_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v_e_2507_);
v___x_2527_ = v___x_2521_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_e_2507_);
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
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v___f_2508_);
lean_dec_ref(v_e_2507_);
v_a_2530_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2518_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2518_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v_e_2507_);
v___x_2538_ = lean_box(0);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
v___x_2539_ = lean_apply_9(v___f_2508_, v___x_2538_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, lean_box(0));
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(lean_object* v_types_2540_, lean_object* v_e_2541_, lean_object* v___f_2542_, lean_object* v_____r_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
uint8_t v_types_boxed_2552_; lean_object* v_res_2553_; 
v_types_boxed_2552_ = lean_unbox(v_types_2540_);
v_res_2553_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(v_types_boxed_2552_, v_e_2541_, v___f_2542_, v_____r_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2553_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2554_; lean_object* v_dummy_2555_; 
v___x_2554_ = lean_box(0);
v_dummy_2555_ = l_Lean_Expr_sort___override(v___x_2554_);
return v_dummy_2555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___redArg(lean_object* v_upperBound_2556_, lean_object* v_fst_2557_, lean_object* v_fvars_2558_, lean_object* v_a_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_a_2570_; uint8_t v___x_2574_; 
v___x_2574_ = lean_nat_dec_lt(v_a_2559_, v_upperBound_2556_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
lean_dec(v_a_2559_);
lean_dec(v_fvars_2558_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_b_2560_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v_binderInfo_2578_; uint8_t v___x_2579_; 
v___x_2576_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2577_ = lean_array_get_borrowed(v___x_2576_, v_fst_2557_, v_a_2559_);
v_binderInfo_2578_ = lean_ctor_get_uint8(v___x_2577_, sizeof(void*)*2);
v___x_2579_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2578_);
if (v___x_2579_ == 0)
{
v_a_2570_ = v_b_2560_;
goto v___jp_2569_;
}
else
{
uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2580_ = 0;
v___x_2581_ = l_Lean_instInhabitedExpr;
v___x_2582_ = lean_array_get_borrowed(v___x_2581_, v_b_2560_, v_a_2559_);
lean_inc(v___x_2582_);
lean_inc(v_fvars_2558_);
v___x_2583_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2558_, v___x_2582_, v___x_2580_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = lean_array_set(v_b_2560_, v_a_2559_, v_a_2584_);
v_a_2570_ = v___x_2585_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v_b_2560_);
lean_dec(v_a_2559_);
lean_dec(v_fvars_2558_);
v_a_2586_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2583_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2583_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
v___jp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_unsigned_to_nat(1u);
v___x_2572_ = lean_nat_add(v_a_2559_, v___x_2571_);
lean_dec(v_a_2559_);
v_a_2559_ = v___x_2572_;
v_b_2560_ = v_a_2570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__8(lean_object* v_fvars_2594_, size_t v_sz_2595_, size_t v_i_2596_, lean_object* v_bs_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
uint8_t v___x_2606_; 
v___x_2606_ = lean_usize_dec_lt(v_i_2596_, v_sz_2595_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
lean_dec(v_fvars_2594_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_bs_2597_);
return v___x_2607_;
}
else
{
uint8_t v___x_2608_; lean_object* v_v_2609_; lean_object* v___x_2610_; 
v___x_2608_ = 0;
v_v_2609_ = lean_array_uget_borrowed(v_bs_2597_, v_i_2596_);
lean_inc(v_v_2609_);
lean_inc(v_fvars_2594_);
v___x_2610_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2594_, v_v_2609_, v___x_2608_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v_bs_x27_2613_; size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = lean_unsigned_to_nat(0u);
v_bs_x27_2613_ = lean_array_uset(v_bs_2597_, v_i_2596_, v___x_2612_);
v___x_2614_ = ((size_t)1ULL);
v___x_2615_ = lean_usize_add(v_i_2596_, v___x_2614_);
v___x_2616_ = lean_array_uset(v_bs_x27_2613_, v_i_2596_, v_a_2611_);
v_i_2596_ = v___x_2615_;
v_bs_2597_ = v___x_2616_;
goto _start;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v_bs_2597_);
lean_dec(v_fvars_2594_);
v_a_2618_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2610_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2610_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2626_, lean_object* v_f_2627_, lean_object* v_args_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
uint8_t v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = 0;
lean_inc_ref(v_f_2627_);
lean_inc(v_fvars_2626_);
v___x_2638_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2626_, v_f_2627_, v___x_2637_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
if (lean_obj_tag(v___x_2638_) == 0)
{
uint8_t v_implicits_2639_; 
v_implicits_2639_ = lean_ctor_get_uint8(v_a_2629_, 2);
if (v_implicits_2639_ == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2641_; 
v_a_2640_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2638_, 1);
lean_inc(v_a_2635_);
lean_inc_ref(v_a_2634_);
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
v___x_2641_ = lean_infer_type(v_f_2627_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2642_, v_args_2628_, v___x_2637_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v_fst_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v_fst_2645_ = lean_ctor_get(v_a_2644_, 0);
lean_inc(v_fst_2645_);
lean_dec(v_a_2644_);
v___x_2646_ = lean_array_get_size(v_args_2628_);
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___redArg(v___x_2646_, v_fst_2645_, v_fvars_2626_, v___x_2647_, v_args_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
lean_dec(v_fst_2645_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2657_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = l_Lean_mkAppN(v_a_2640_, v_a_2649_);
lean_dec(v_a_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2653_);
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_a_2640_);
v_a_2658_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2648_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2648_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
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
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v_a_2640_);
lean_dec_ref(v_args_2628_);
lean_dec(v_fvars_2626_);
v_a_2666_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2643_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2643_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_dec(v_a_2640_);
lean_dec_ref(v_args_2628_);
lean_dec(v_fvars_2626_);
return v___x_2641_;
}
}
else
{
lean_object* v_a_2674_; size_t v_sz_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
lean_dec_ref(v_f_2627_);
v_a_2674_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2638_, 1);
v_sz_2675_ = lean_array_size(v_args_2628_);
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__8(v_fvars_2626_, v_sz_2675_, v___x_2676_, v_args_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2686_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2686_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2686_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = l_Lean_mkAppN(v_a_2674_, v_a_2678_);
lean_dec(v_a_2678_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2682_);
v___x_2684_ = v___x_2680_;
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
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec(v_a_2674_);
v_a_2687_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2677_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2677_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_2628_);
lean_dec_ref(v_f_2627_);
lean_dec(v_fvars_2626_);
return v___x_2638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2695_, lean_object* v_f_2696_, lean_object* v_args_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2695_, v_f_2696_, v_args_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2707_, lean_object* v_b_2708_, uint8_t v___x_2709_, lean_object* v_mk_2710_, lean_object* v_a_2711_, lean_object* v_x_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_inc_ref(v_x_2712_);
v___x_2721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_x_2712_);
lean_ctor_set(v___x_2721_, 1, v_fvars_2707_);
v___x_2722_ = lean_expr_instantiate1(v_b_2708_, v_x_2712_);
v___x_2723_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2721_, v___x_2722_, v___x_2709_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2723_) == 0)
{
uint8_t v_lift_2724_; 
v_lift_2724_ = lean_ctor_get_uint8(v___y_2713_, 10);
if (v_lift_2724_ == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2737_; 
v_a_2725_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2727_ = v___x_2723_;
v_isShared_2728_ = v_isSharedCheck_2737_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2737_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2729_ = lean_unsigned_to_nat(1u);
v___x_2730_ = lean_mk_empty_array_with_capacity(v___x_2729_);
v___x_2731_ = lean_array_push(v___x_2730_, v_x_2712_);
v___x_2732_ = lean_expr_abstract(v_a_2725_, v___x_2731_);
lean_dec_ref(v___x_2731_);
lean_dec(v_a_2725_);
v___x_2733_ = lean_apply_2(v_mk_2710_, v_a_2711_, v___x_2732_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2733_);
v___x_2735_ = v___x_2727_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_a_2738_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2723_, 1);
v___x_2739_ = l_Lean_Expr_fvarId_x21(v_x_2712_);
v___x_2740_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2739_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2754_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2754_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2754_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2745_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2741_, v_a_2738_);
lean_dec(v_a_2741_);
v___x_2746_ = lean_unsigned_to_nat(1u);
v___x_2747_ = lean_mk_empty_array_with_capacity(v___x_2746_);
v___x_2748_ = lean_array_push(v___x_2747_, v_x_2712_);
v___x_2749_ = lean_expr_abstract(v___x_2745_, v___x_2748_);
lean_dec_ref(v___x_2748_);
lean_dec_ref(v___x_2745_);
v___x_2750_ = lean_apply_2(v_mk_2710_, v_a_2711_, v___x_2749_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2750_);
v___x_2752_ = v___x_2743_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_a_2738_);
lean_dec_ref(v_x_2712_);
lean_dec_ref(v_a_2711_);
lean_dec_ref(v_mk_2710_);
v_a_2755_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2740_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2740_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_2712_);
lean_dec_ref(v_a_2711_);
lean_dec_ref(v_mk_2710_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2763_, lean_object* v_b_2764_, lean_object* v___x_2765_, lean_object* v_mk_2766_, lean_object* v_a_2767_, lean_object* v_x_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
uint8_t v___x_57260__boxed_2777_; lean_object* v_res_2778_; 
v___x_57260__boxed_2777_ = lean_unbox(v___x_2765_);
v_res_2778_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2763_, v_b_2764_, v___x_57260__boxed_2777_, v_mk_2766_, v_a_2767_, v_x_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec_ref(v_b_2764_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2779_, lean_object* v_n_2780_, lean_object* v_t_2781_, lean_object* v_b_2782_, uint8_t v_i_2783_, lean_object* v_mk_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = 0;
lean_inc(v_fvars_2779_);
v___x_2794_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2779_, v_t_2781_, v___x_2793_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2794_) == 0)
{
uint8_t v_underBinder_2795_; 
v_underBinder_2795_ = lean_ctor_get_uint8(v_a_2785_, 4);
if (v_underBinder_2795_ == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v_n_2780_);
lean_dec(v_fvars_2779_);
v_a_2796_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2798_ = v___x_2794_;
v_isShared_2799_ = v_isSharedCheck_2804_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2794_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2804_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = lean_apply_2(v_mk_2784_, v_a_2796_, v_b_2782_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2802_ = v___x_2798_;
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
else
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___f_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; 
v_a_2805_ = lean_ctor_get(v___x_2794_, 0);
lean_inc_n(v_a_2805_, 2);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2806_ = lean_box(v___x_2793_);
v___f_2807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2807_, 0, v_fvars_2779_);
lean_closure_set(v___f_2807_, 1, v_b_2782_);
lean_closure_set(v___f_2807_, 2, v___x_2806_);
lean_closure_set(v___f_2807_, 3, v_mk_2784_);
lean_closure_set(v___f_2807_, 4, v_a_2805_);
v___x_2808_ = 0;
v___x_2809_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2780_, v_i_2783_, v_a_2805_, v___f_2807_, v___x_2808_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
return v___x_2809_;
}
}
else
{
lean_dec_ref(v_mk_2784_);
lean_dec_ref(v_b_2782_);
lean_dec(v_n_2780_);
lean_dec(v_fvars_2779_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2810_, lean_object* v_n_2811_, lean_object* v_t_2812_, lean_object* v_b_2813_, lean_object* v_i_2814_, lean_object* v_mk_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
uint8_t v_i_boxed_2824_; lean_object* v_res_2825_; 
v_i_boxed_2824_ = lean_unbox(v_i_2814_);
v_res_2825_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2810_, v_n_2811_, v_t_2812_, v_b_2813_, v_i_boxed_2824_, v_mk_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2826_, lean_object* v_e_2827_, lean_object* v_topLevel_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
uint8_t v_topLevel_boxed_2837_; lean_object* v_res_2838_; 
v_topLevel_boxed_2837_ = lean_unbox(v_topLevel_2828_);
v_res_2838_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2826_, v_e_2827_, v_topLevel_boxed_2837_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
return v_res_2838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2843_ = lean_unsigned_to_nat(27u);
v___x_2844_ = lean_unsigned_to_nat(1964u);
v___x_2845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2847_ = l_mkPanicMessageWithDecl(v___x_2846_, v___x_2845_, v___x_2844_, v___x_2843_, v___x_2842_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2848_, lean_object* v_fvars_2849_, lean_object* v_b_2850_, uint8_t v___x_2851_, lean_object* v_e_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, uint8_t v_isLet_2855_, uint8_t v_topLevel_2856_, lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
if (v_fst_2848_ == 0)
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_inc_ref(v_x_2857_);
v___x_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2866_, 0, v_x_2857_);
lean_ctor_set(v___x_2866_, 1, v_fvars_2849_);
v___x_2867_ = lean_expr_instantiate1(v_b_2850_, v_x_2857_);
v___x_2868_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2866_, v___x_2867_, v___x_2851_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2868_) == 0)
{
if (lean_obj_tag(v_e_2852_) == 8)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2904_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2904_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2904_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v_declName_2873_; lean_object* v_type_2874_; lean_object* v_value_2875_; lean_object* v_body_2876_; uint8_t v_nondep_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___y_2883_; size_t v___x_2898_; size_t v___x_2899_; uint8_t v___x_2900_; 
v_declName_2873_ = lean_ctor_get(v_e_2852_, 0);
v_type_2874_ = lean_ctor_get(v_e_2852_, 1);
v_value_2875_ = lean_ctor_get(v_e_2852_, 2);
v_body_2876_ = lean_ctor_get(v_e_2852_, 3);
v_nondep_2877_ = lean_ctor_get_uint8(v_e_2852_, sizeof(void*)*4 + 8);
v___x_2878_ = lean_unsigned_to_nat(1u);
v___x_2879_ = lean_mk_empty_array_with_capacity(v___x_2878_);
v___x_2880_ = lean_array_push(v___x_2879_, v_x_2857_);
v___x_2881_ = lean_expr_abstract(v_a_2869_, v___x_2880_);
lean_dec_ref(v___x_2880_);
lean_dec(v_a_2869_);
v___x_2898_ = lean_ptr_addr(v_type_2874_);
v___x_2899_ = lean_ptr_addr(v_a_2853_);
v___x_2900_ = lean_usize_dec_eq(v___x_2898_, v___x_2899_);
if (v___x_2900_ == 0)
{
v___y_2883_ = v___x_2900_;
goto v___jp_2882_;
}
else
{
size_t v___x_2901_; size_t v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = lean_ptr_addr(v_value_2875_);
v___x_2902_ = lean_ptr_addr(v_a_2854_);
v___x_2903_ = lean_usize_dec_eq(v___x_2901_, v___x_2902_);
v___y_2883_ = v___x_2903_;
goto v___jp_2882_;
}
v___jp_2882_:
{
if (v___y_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_inc(v_declName_2873_);
lean_dec_ref_known(v_e_2852_, 4);
v___x_2884_ = l_Lean_Expr_letE___override(v_declName_2873_, v_a_2853_, v_a_2854_, v___x_2881_, v_nondep_2877_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2884_);
v___x_2886_ = v___x_2871_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
else
{
size_t v___x_2888_; size_t v___x_2889_; uint8_t v___x_2890_; 
v___x_2888_ = lean_ptr_addr(v_body_2876_);
v___x_2889_ = lean_ptr_addr(v___x_2881_);
v___x_2890_ = lean_usize_dec_eq(v___x_2888_, v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
lean_inc(v_declName_2873_);
lean_dec_ref_known(v_e_2852_, 4);
v___x_2891_ = l_Lean_Expr_letE___override(v_declName_2873_, v_a_2853_, v_a_2854_, v___x_2881_, v_nondep_2877_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2891_);
v___x_2893_ = v___x_2871_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
else
{
lean_object* v___x_2896_; 
lean_dec_ref(v___x_2881_);
lean_dec_ref(v_a_2854_);
lean_dec_ref(v_a_2853_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v_e_2852_);
v___x_2896_ = v___x_2871_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_e_2852_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
else
{
lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v_x_2857_);
lean_dec_ref(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec_ref(v_e_2852_);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v___x_2868_, 0);
lean_dec(v_unused_2914_);
v___x_2906_ = v___x_2868_;
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
else
{
lean_dec(v___x_2868_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2909_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v___x_2908_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
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
lean_dec_ref(v_x_2857_);
lean_dec_ref(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec_ref(v_e_2852_);
return v___x_2868_;
}
}
else
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec_ref(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec_ref(v_e_2852_);
v___x_2915_ = l_Lean_Expr_fvarId_x21(v_x_2857_);
v___x_2916_ = l_Lean_FVarId_getDecl___redArg(v___x_2915_, v___y_2861_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
v___x_2918_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2917_, v_isLet_2855_, v___y_2858_, v___y_2860_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec_ref_known(v___x_2918_, 1);
v___x_2919_ = lean_expr_instantiate1(v_b_2850_, v_x_2857_);
lean_dec_ref(v_x_2857_);
v___x_2920_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2849_, v___x_2919_, v_topLevel_2856_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
return v___x_2920_;
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v_x_2857_);
lean_dec(v_fvars_2849_);
v_a_2921_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2918_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2918_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref(v_x_2857_);
lean_dec(v_fvars_2849_);
v_a_2929_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2916_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2916_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2937_ = _args[0];
lean_object* v_fvars_2938_ = _args[1];
lean_object* v_b_2939_ = _args[2];
lean_object* v___x_2940_ = _args[3];
lean_object* v_e_2941_ = _args[4];
lean_object* v_a_2942_ = _args[5];
lean_object* v_a_2943_ = _args[6];
lean_object* v_isLet_2944_ = _args[7];
lean_object* v_topLevel_2945_ = _args[8];
lean_object* v_x_2946_ = _args[9];
lean_object* v___y_2947_ = _args[10];
lean_object* v___y_2948_ = _args[11];
lean_object* v___y_2949_ = _args[12];
lean_object* v___y_2950_ = _args[13];
lean_object* v___y_2951_ = _args[14];
lean_object* v___y_2952_ = _args[15];
lean_object* v___y_2953_ = _args[16];
lean_object* v___y_2954_ = _args[17];
_start:
{
uint8_t v_fst_57405__boxed_2955_; uint8_t v___x_57406__boxed_2956_; uint8_t v_isLet_boxed_2957_; uint8_t v_topLevel_boxed_2958_; lean_object* v_res_2959_; 
v_fst_57405__boxed_2955_ = lean_unbox(v_fst_2937_);
v___x_57406__boxed_2956_ = lean_unbox(v___x_2940_);
v_isLet_boxed_2957_ = lean_unbox(v_isLet_2944_);
v_topLevel_boxed_2958_ = lean_unbox(v_topLevel_2945_);
v_res_2959_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_57405__boxed_2955_, v_fvars_2938_, v_b_2939_, v___x_57406__boxed_2956_, v_e_2941_, v_a_2942_, v_a_2943_, v_isLet_boxed_2957_, v_topLevel_boxed_2958_, v_x_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec_ref(v_b_2939_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2960_, lean_object* v_e_2961_, uint8_t v_isLet_2962_, lean_object* v_n_2963_, lean_object* v_t_2964_, lean_object* v_v_2965_, lean_object* v_b_2966_, uint8_t v_topLevel_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; uint8_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = 0;
lean_inc(v_fvars_2960_);
v___x_2991_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2960_, v_t_2964_, v___x_2990_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3110_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_3110_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3110_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; 
lean_inc(v_fvars_2960_);
v___x_2996_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2960_, v_v_2965_, v___x_2990_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3109_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3109_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3109_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___y_3002_; uint8_t v___y_3003_; lean_object* v___y_3004_; uint8_t v___y_3005_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; uint8_t v_descend_3049_; uint8_t v_underBinder_3050_; uint8_t v_usedOnly_3051_; uint8_t v_merge_3052_; uint8_t v_lift_3053_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; uint8_t v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; uint8_t v___y_3091_; 
v_descend_3049_ = lean_ctor_get_uint8(v_a_2968_, 3);
v_underBinder_3050_ = lean_ctor_get_uint8(v_a_2968_, 4);
v_usedOnly_3051_ = lean_ctor_get_uint8(v_a_2968_, 5);
v_merge_3052_ = lean_ctor_get_uint8(v_a_2968_, 6);
v_lift_3053_ = lean_ctor_get_uint8(v_a_2968_, 10);
if (v_usedOnly_3051_ == 0)
{
v___y_3091_ = v___x_2990_;
goto v___jp_3090_;
}
else
{
uint8_t v___x_3107_; 
v___x_3107_ = l_Lean_Expr_hasLooseBVars(v_b_2966_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_del_object(v___x_2999_);
lean_dec(v_a_2997_);
lean_del_object(v___x_2994_);
lean_dec(v_a_2992_);
lean_dec(v_n_2963_);
lean_dec_ref(v_e_2961_);
v___x_3108_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2960_, v_b_2966_, v_topLevel_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3108_;
}
else
{
v___y_3091_ = v___x_2990_;
goto v___jp_3090_;
}
}
v___jp_3001_:
{
if (v___y_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_e_2961_);
v___x_3006_ = l_Lean_Expr_letE___override(v___y_3004_, v_a_2992_, v_a_2997_, v_b_2966_, v___y_3003_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3006_);
v___x_3008_ = v___x_2999_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
else
{
size_t v___x_3010_; size_t v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = lean_ptr_addr(v___y_3002_);
lean_dec_ref(v___y_3002_);
v___x_3011_ = lean_ptr_addr(v_b_2966_);
v___x_3012_ = lean_usize_dec_eq(v___x_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
lean_dec_ref(v_e_2961_);
v___x_3013_ = l_Lean_Expr_letE___override(v___y_3004_, v_a_2992_, v_a_2997_, v_b_2966_, v___y_3003_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3013_);
v___x_3015_ = v___x_2999_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
else
{
lean_object* v___x_3018_; 
lean_dec(v___y_3004_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec_ref(v_b_2966_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v_e_2961_);
v___x_3018_ = v___x_2999_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_e_2961_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
v___jp_3020_:
{
if (lean_obj_tag(v_e_2961_) == 8)
{
lean_object* v_declName_3021_; lean_object* v_type_3022_; lean_object* v_value_3023_; lean_object* v_body_3024_; uint8_t v_nondep_3025_; size_t v___x_3026_; size_t v___x_3027_; uint8_t v___x_3028_; 
lean_del_object(v___x_2994_);
v_declName_3021_ = lean_ctor_get(v_e_2961_, 0);
v_type_3022_ = lean_ctor_get(v_e_2961_, 1);
v_value_3023_ = lean_ctor_get(v_e_2961_, 2);
v_body_3024_ = lean_ctor_get(v_e_2961_, 3);
v_nondep_3025_ = lean_ctor_get_uint8(v_e_2961_, sizeof(void*)*4 + 8);
v___x_3026_ = lean_ptr_addr(v_type_3022_);
v___x_3027_ = lean_ptr_addr(v_a_2992_);
v___x_3028_ = lean_usize_dec_eq(v___x_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_inc(v_declName_3021_);
lean_inc_ref(v_body_3024_);
v___y_3002_ = v_body_3024_;
v___y_3003_ = v_nondep_3025_;
v___y_3004_ = v_declName_3021_;
v___y_3005_ = v___x_3028_;
goto v___jp_3001_;
}
else
{
size_t v___x_3029_; size_t v___x_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_ptr_addr(v_value_3023_);
v___x_3030_ = lean_ptr_addr(v_a_2997_);
v___x_3031_ = lean_usize_dec_eq(v___x_3029_, v___x_3030_);
lean_inc(v_declName_3021_);
lean_inc_ref(v_body_3024_);
v___y_3002_ = v_body_3024_;
v___y_3003_ = v_nondep_3025_;
v___y_3004_ = v_declName_3021_;
v___y_3005_ = v___x_3031_;
goto v___jp_3001_;
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_del_object(v___x_2999_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec_ref(v_b_2966_);
lean_dec_ref(v_e_2961_);
v___x_3032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_3033_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v___x_3032_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_3033_);
v___x_3035_ = v___x_2994_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
v___jp_3037_:
{
uint8_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = 0;
v___x_3048_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v___y_3038_, v_a_2992_, v_a_2997_, v___y_3039_, v___x_2990_, v___x_3047_, v___y_3043_, v___y_3044_, v___y_3042_, v___y_3041_, v___y_3040_, v___y_3045_, v___y_3046_);
return v___x_3048_;
}
v___jp_3054_:
{
if (v_underBinder_3050_ == 0)
{
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
goto v___jp_3020_;
}
else
{
if (v_descend_3049_ == 0)
{
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
goto v___jp_3020_;
}
else
{
lean_del_object(v___x_2999_);
lean_del_object(v___x_2994_);
lean_dec_ref(v_b_2966_);
lean_dec_ref(v_e_2961_);
v___y_3038_ = v___y_3055_;
v___y_3039_ = v___y_3056_;
v___y_3040_ = v___y_3057_;
v___y_3041_ = v___y_3058_;
v___y_3042_ = v___y_3059_;
v___y_3043_ = v___y_3060_;
v___y_3044_ = v___y_3061_;
v___y_3045_ = v___y_3062_;
v___y_3046_ = v___y_3063_;
goto v___jp_3037_;
}
}
}
v___jp_3064_:
{
lean_object* v___x_3073_; 
lean_inc(v_a_2997_);
lean_inc(v_a_2992_);
v___x_3073_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2960_, v_n_2963_, v_a_2992_, v_a_2997_, v___y_3066_, v___y_3068_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v_fst_3075_; lean_object* v_snd_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___f_3080_; uint8_t v___x_3081_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v_fst_3075_ = lean_ctor_get(v_a_3074_, 0);
lean_inc_n(v_fst_3075_, 2);
v_snd_3076_ = lean_ctor_get(v_a_3074_, 1);
lean_inc(v_snd_3076_);
lean_dec(v_a_3074_);
v___x_3077_ = lean_box(v___x_2990_);
v___x_3078_ = lean_box(v_isLet_2962_);
v___x_3079_ = lean_box(v_topLevel_2967_);
lean_inc(v_a_2997_);
lean_inc(v_a_2992_);
lean_inc_ref(v_e_2961_);
lean_inc_ref(v_b_2966_);
v___f_3080_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3080_, 0, v_fst_3075_);
lean_closure_set(v___f_3080_, 1, v_fvars_2960_);
lean_closure_set(v___f_3080_, 2, v_b_2966_);
lean_closure_set(v___f_3080_, 3, v___x_3077_);
lean_closure_set(v___f_3080_, 4, v_e_2961_);
lean_closure_set(v___f_3080_, 5, v_a_2992_);
lean_closure_set(v___f_3080_, 6, v_a_2997_);
lean_closure_set(v___f_3080_, 7, v___x_3078_);
lean_closure_set(v___f_3080_, 8, v___x_3079_);
v___x_3081_ = lean_unbox(v_fst_3075_);
lean_dec(v_fst_3075_);
if (v___x_3081_ == 0)
{
v___y_3055_ = v_snd_3076_;
v___y_3056_ = v___f_3080_;
v___y_3057_ = v___y_3070_;
v___y_3058_ = v___y_3069_;
v___y_3059_ = v___y_3068_;
v___y_3060_ = v___y_3066_;
v___y_3061_ = v___y_3067_;
v___y_3062_ = v___y_3071_;
v___y_3063_ = v___y_3072_;
goto v___jp_3054_;
}
else
{
if (v___y_3065_ == 0)
{
lean_del_object(v___x_2999_);
lean_del_object(v___x_2994_);
lean_dec_ref(v_b_2966_);
lean_dec_ref(v_e_2961_);
v___y_3038_ = v_snd_3076_;
v___y_3039_ = v___f_3080_;
v___y_3040_ = v___y_3070_;
v___y_3041_ = v___y_3069_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3066_;
v___y_3044_ = v___y_3067_;
v___y_3045_ = v___y_3071_;
v___y_3046_ = v___y_3072_;
goto v___jp_3037_;
}
else
{
v___y_3055_ = v_snd_3076_;
v___y_3056_ = v___f_3080_;
v___y_3057_ = v___y_3070_;
v___y_3058_ = v___y_3069_;
v___y_3059_ = v___y_3068_;
v___y_3060_ = v___y_3066_;
v___y_3061_ = v___y_3067_;
v___y_3062_ = v___y_3071_;
v___y_3063_ = v___y_3072_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_del_object(v___x_2999_);
lean_dec(v_a_2997_);
lean_del_object(v___x_2994_);
lean_dec(v_a_2992_);
lean_dec_ref(v_b_2966_);
lean_dec_ref(v_e_2961_);
lean_dec(v_fvars_2960_);
v_a_3082_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3073_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3073_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
v___jp_3090_:
{
if (v_merge_3052_ == 0)
{
v___y_3065_ = v___y_3091_;
v___y_3066_ = v_a_2968_;
v___y_3067_ = v_a_2969_;
v___y_3068_ = v_a_2970_;
v___y_3069_ = v_a_2971_;
v___y_3070_ = v_a_2972_;
v___y_3071_ = v_a_2973_;
v___y_3072_ = v_a_2974_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3092_; lean_object* v_valueMap_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_st_ref_get(v_a_2970_);
v_valueMap_3093_ = lean_ctor_get(v___x_3092_, 2);
lean_inc_ref(v_valueMap_3093_);
lean_dec(v___x_3092_);
v___x_3094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___redArg(v_valueMap_3093_, v_a_2997_);
lean_dec_ref(v_valueMap_3093_);
if (lean_obj_tag(v___x_3094_) == 1)
{
lean_del_object(v___x_2999_);
lean_dec(v_a_2997_);
lean_del_object(v___x_2994_);
lean_dec(v_a_2992_);
lean_dec(v_n_2963_);
lean_dec_ref(v_e_2961_);
if (v_isLet_2962_ == 0)
{
lean_object* v_val_3095_; 
v_val_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_val_3095_);
lean_dec_ref_known(v___x_3094_, 1);
v___y_2977_ = v_val_3095_;
v___y_2978_ = v_a_2968_;
v___y_2979_ = v_a_2969_;
v___y_2980_ = v_a_2970_;
v___y_2981_ = v_a_2971_;
v___y_2982_ = v_a_2972_;
v___y_2983_ = v_a_2973_;
v___y_2984_ = v_a_2974_;
goto v___jp_2976_;
}
else
{
if (v_lift_3053_ == 0)
{
lean_object* v_val_3096_; 
v_val_3096_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v___x_3094_, 1);
v___y_2977_ = v_val_3096_;
v___y_2978_ = v_a_2968_;
v___y_2979_ = v_a_2969_;
v___y_2980_ = v_a_2970_;
v___y_2981_ = v_a_2971_;
v___y_2982_ = v_a_2972_;
v___y_2983_ = v_a_2973_;
v___y_2984_ = v_a_2974_;
goto v___jp_2976_;
}
else
{
lean_object* v_val_3097_; lean_object* v___x_3098_; 
v_val_3097_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3098_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_3097_, v_a_2970_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_dec_ref_known(v___x_3098_, 1);
v___y_2977_ = v_val_3097_;
v___y_2978_ = v_a_2968_;
v___y_2979_ = v_a_2969_;
v___y_2980_ = v_a_2970_;
v___y_2981_ = v_a_2971_;
v___y_2982_ = v_a_2972_;
v___y_2983_ = v_a_2973_;
v___y_2984_ = v_a_2974_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_val_3097_);
lean_dec_ref(v_b_2966_);
lean_dec(v_fvars_2960_);
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3098_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3098_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
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
}
}
else
{
lean_dec(v___x_3094_);
v___y_3065_ = v___y_3091_;
v___y_3066_ = v_a_2968_;
v___y_3067_ = v_a_2969_;
v___y_3068_ = v_a_2970_;
v___y_3069_ = v_a_2971_;
v___y_3070_ = v_a_2972_;
v___y_3071_ = v_a_2973_;
v___y_3072_ = v_a_2974_;
goto v___jp_3064_;
}
}
}
}
}
else
{
lean_del_object(v___x_2994_);
lean_dec(v_a_2992_);
lean_dec_ref(v_b_2966_);
lean_dec(v_n_2963_);
lean_dec_ref(v_e_2961_);
lean_dec(v_fvars_2960_);
return v___x_2996_;
}
}
}
else
{
lean_dec_ref(v_b_2966_);
lean_dec_ref(v_v_2965_);
lean_dec(v_n_2963_);
lean_dec_ref(v_e_2961_);
lean_dec(v_fvars_2960_);
return v___x_2991_;
}
v___jp_2976_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_inc(v___y_2977_);
v___x_2985_ = l_Lean_Expr_fvar___override(v___y_2977_);
v___x_2986_ = lean_expr_instantiate1(v_b_2966_, v___x_2985_);
lean_dec_ref(v___x_2985_);
lean_dec_ref(v_b_2966_);
v___x_2987_ = lean_box(v_topLevel_2967_);
v___x_2988_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2988_, 0, v_fvars_2960_);
lean_closure_set(v___x_2988_, 1, v___x_2986_);
lean_closure_set(v___x_2988_, 2, v___x_2987_);
v___x_2989_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2977_, v___x_2988_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2977_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_3111_, lean_object* v_struct_3112_, lean_object* v___y_3113_, lean_object* v_typeName_3114_, lean_object* v_idx_3115_, lean_object* v_e_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
uint8_t v___y_57181__boxed_3125_; lean_object* v_res_3126_; 
v___y_57181__boxed_3125_ = lean_unbox(v___y_3113_);
v_res_3126_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_3111_, v_struct_3112_, v___y_57181__boxed_3125_, v_typeName_3114_, v_idx_3115_, v_e_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3126_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3130_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_3131_ = lean_unsigned_to_nat(75u);
v___x_3132_ = lean_unsigned_to_nat(229u);
v___x_3133_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_3134_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_3135_ = l_mkPanicMessageWithDecl(v___x_3134_, v___x_3133_, v___x_3132_, v___x_3131_, v___x_3130_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_3136_, lean_object* v_e_3137_, lean_object* v_fvars_3138_, uint8_t v___x_3139_, uint8_t v_topLevel_3140_, uint8_t v___y_3141_, lean_object* v_____r_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_k_3152_; 
switch(lean_obj_tag(v_e_3137_))
{
case 5:
{
lean_object* v___x_3155_; lean_object* v_dummy_3156_; lean_object* v_nargs_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3155_ = l_Lean_Expr_getAppFn(v_e_3137_);
v_dummy_3156_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_3157_ = l_Lean_Expr_getAppNumArgs(v_e_3137_);
lean_inc(v_nargs_3157_);
v___x_3158_ = lean_mk_array(v_nargs_3157_, v_dummy_3156_);
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = lean_nat_sub(v_nargs_3157_, v___x_3159_);
lean_dec(v_nargs_3157_);
lean_inc_ref(v_e_3137_);
v___x_3161_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3137_, v___x_3158_, v___x_3160_);
v___x_3162_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_3162_, 0, v_fvars_3138_);
lean_closure_set(v___x_3162_, 1, v___x_3155_);
lean_closure_set(v___x_3162_, 2, v___x_3161_);
v_k_3152_ = v___x_3162_;
goto v___jp_3151_;
}
case 6:
{
lean_object* v_binderName_3163_; lean_object* v_binderType_3164_; lean_object* v_body_3165_; uint8_t v_binderInfo_3166_; lean_object* v___x_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_binderName_3163_ = lean_ctor_get(v_e_3137_, 0);
v_binderType_3164_ = lean_ctor_get(v_e_3137_, 1);
v_body_3165_ = lean_ctor_get(v_e_3137_, 2);
v_binderInfo_3166_ = lean_ctor_get_uint8(v_e_3137_, sizeof(void*)*3 + 8);
v___x_3167_ = lean_box(v_binderInfo_3166_);
lean_inc_ref_n(v_body_3165_, 2);
lean_inc_ref_n(v_binderType_3164_, 2);
lean_inc_ref(v_e_3137_);
lean_inc_n(v_binderName_3163_, 2);
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3168_, 0, v_binderName_3163_);
lean_closure_set(v___f_3168_, 1, v___x_3167_);
lean_closure_set(v___f_3168_, 2, v_e_3137_);
lean_closure_set(v___f_3168_, 3, v_binderType_3164_);
lean_closure_set(v___f_3168_, 4, v_body_3165_);
v___x_3169_ = lean_box(v_binderInfo_3166_);
v___x_3170_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_3170_, 0, v_fvars_3138_);
lean_closure_set(v___x_3170_, 1, v_binderName_3163_);
lean_closure_set(v___x_3170_, 2, v_binderType_3164_);
lean_closure_set(v___x_3170_, 3, v_body_3165_);
lean_closure_set(v___x_3170_, 4, v___x_3169_);
lean_closure_set(v___x_3170_, 5, v___f_3168_);
v_k_3152_ = v___x_3170_;
goto v___jp_3151_;
}
case 7:
{
lean_object* v_binderName_3171_; lean_object* v_binderType_3172_; lean_object* v_body_3173_; uint8_t v_binderInfo_3174_; lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_binderName_3171_ = lean_ctor_get(v_e_3137_, 0);
v_binderType_3172_ = lean_ctor_get(v_e_3137_, 1);
v_body_3173_ = lean_ctor_get(v_e_3137_, 2);
v_binderInfo_3174_ = lean_ctor_get_uint8(v_e_3137_, sizeof(void*)*3 + 8);
v___x_3175_ = lean_box(v_binderInfo_3174_);
lean_inc_ref_n(v_body_3173_, 2);
lean_inc_ref_n(v_binderType_3172_, 2);
lean_inc_ref(v_e_3137_);
lean_inc_n(v_binderName_3171_, 2);
v___f_3176_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_3176_, 0, v_binderName_3171_);
lean_closure_set(v___f_3176_, 1, v___x_3175_);
lean_closure_set(v___f_3176_, 2, v_e_3137_);
lean_closure_set(v___f_3176_, 3, v_binderType_3172_);
lean_closure_set(v___f_3176_, 4, v_body_3173_);
v___x_3177_ = lean_box(v_binderInfo_3174_);
v___x_3178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_3178_, 0, v_fvars_3138_);
lean_closure_set(v___x_3178_, 1, v_binderName_3171_);
lean_closure_set(v___x_3178_, 2, v_binderType_3172_);
lean_closure_set(v___x_3178_, 3, v_body_3173_);
lean_closure_set(v___x_3178_, 4, v___x_3177_);
lean_closure_set(v___x_3178_, 5, v___f_3176_);
v_k_3152_ = v___x_3178_;
goto v___jp_3151_;
}
case 8:
{
uint8_t v_nondep_3179_; 
v_nondep_3179_ = lean_ctor_get_uint8(v_e_3137_, sizeof(void*)*4 + 8);
if (v_nondep_3179_ == 0)
{
lean_object* v_declName_3180_; lean_object* v_type_3181_; lean_object* v_value_3182_; lean_object* v_body_3183_; lean_object* v___x_3184_; 
v_declName_3180_ = lean_ctor_get(v_e_3137_, 0);
lean_inc(v_declName_3180_);
v_type_3181_ = lean_ctor_get(v_e_3137_, 1);
lean_inc_ref(v_type_3181_);
v_value_3182_ = lean_ctor_get(v_e_3137_, 2);
lean_inc_ref(v_value_3182_);
v_body_3183_ = lean_ctor_get(v_e_3137_, 3);
lean_inc_ref(v_body_3183_);
v___x_3184_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3138_, v_e_3137_, v___x_3139_, v_declName_3180_, v_type_3181_, v_value_3182_, v_body_3183_, v_topLevel_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
return v___x_3184_;
}
else
{
lean_object* v_declName_3185_; lean_object* v_type_3186_; lean_object* v_value_3187_; lean_object* v_body_3188_; lean_object* v___x_3189_; 
v_declName_3185_ = lean_ctor_get(v_e_3137_, 0);
lean_inc(v_declName_3185_);
v_type_3186_ = lean_ctor_get(v_e_3137_, 1);
lean_inc_ref(v_type_3186_);
v_value_3187_ = lean_ctor_get(v_e_3137_, 2);
lean_inc_ref(v_value_3187_);
v_body_3188_ = lean_ctor_get(v_e_3137_, 3);
lean_inc_ref(v_body_3188_);
v___x_3189_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3138_, v_e_3137_, v___y_3141_, v_declName_3185_, v_type_3186_, v_value_3187_, v_body_3188_, v_topLevel_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
return v___x_3189_;
}
}
case 10:
{
lean_object* v_data_3190_; lean_object* v_expr_3191_; lean_object* v___x_3192_; 
v_data_3190_ = lean_ctor_get(v_e_3137_, 0);
v_expr_3191_ = lean_ctor_get(v_e_3137_, 1);
lean_inc_ref(v_expr_3191_);
v___x_3192_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3138_, v_expr_3191_, v_topLevel_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3207_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
size_t v___x_3197_; size_t v___x_3198_; uint8_t v___x_3199_; 
v___x_3197_ = lean_ptr_addr(v_expr_3191_);
v___x_3198_ = lean_ptr_addr(v_a_3193_);
v___x_3199_ = lean_usize_dec_eq(v___x_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3202_; 
lean_inc(v_data_3190_);
lean_dec_ref_known(v_e_3137_, 2);
v___x_3200_ = l_Lean_Expr_mdata___override(v_data_3190_, v_a_3193_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3200_);
v___x_3202_ = v___x_3195_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
else
{
lean_object* v___x_3205_; 
lean_dec(v_a_3193_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_e_3137_);
v___x_3205_ = v___x_3195_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_e_3137_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3137_, 2);
return v___x_3192_;
}
}
case 11:
{
lean_object* v_typeName_3208_; lean_object* v_idx_3209_; lean_object* v_struct_3210_; lean_object* v___x_3211_; lean_object* v___f_3212_; 
v_typeName_3208_ = lean_ctor_get(v_e_3137_, 0);
v_idx_3209_ = lean_ctor_get(v_e_3137_, 1);
v_struct_3210_ = lean_ctor_get(v_e_3137_, 2);
v___x_3211_ = lean_box(v___y_3141_);
lean_inc_ref(v_e_3137_);
lean_inc(v_idx_3209_);
lean_inc(v_typeName_3208_);
lean_inc_ref(v_struct_3210_);
v___f_3212_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_3212_, 0, v_fvars_3138_);
lean_closure_set(v___f_3212_, 1, v_struct_3210_);
lean_closure_set(v___f_3212_, 2, v___x_3211_);
lean_closure_set(v___f_3212_, 3, v_typeName_3208_);
lean_closure_set(v___f_3212_, 4, v_idx_3209_);
lean_closure_set(v___f_3212_, 5, v_e_3137_);
v_k_3152_ = v___f_3212_;
goto v___jp_3151_;
}
default: 
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_dec(v_fvars_3138_);
lean_dec_ref(v_e_3137_);
v___x_3213_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_3214_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__5(v___x_3213_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
return v___x_3214_;
}
}
v___jp_3151_:
{
if (v_descend_3136_ == 0)
{
lean_object* v___x_3153_; 
lean_dec_ref(v_k_3152_);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_e_3137_);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; 
lean_dec_ref(v_e_3137_);
lean_inc(v___y_3149_);
lean_inc_ref(v___y_3148_);
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
lean_inc(v___y_3145_);
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
v___x_3154_ = lean_apply_8(v_k_3152_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, lean_box(0));
return v___x_3154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_3215_, lean_object* v_e_3216_, lean_object* v_fvars_3217_, lean_object* v___x_3218_, lean_object* v_topLevel_3219_, lean_object* v___y_3220_, lean_object* v_____r_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
uint8_t v_descend_boxed_3230_; uint8_t v___x_57334__boxed_3231_; uint8_t v_topLevel_boxed_3232_; uint8_t v___y_57335__boxed_3233_; lean_object* v_res_3234_; 
v_descend_boxed_3230_ = lean_unbox(v_descend_3215_);
v___x_57334__boxed_3231_ = lean_unbox(v___x_3218_);
v_topLevel_boxed_3232_ = lean_unbox(v_topLevel_3219_);
v___y_57335__boxed_3233_ = lean_unbox(v___y_3220_);
v_res_3234_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_3230_, v_e_3216_, v_fvars_3217_, v___x_57334__boxed_3231_, v_topLevel_boxed_3232_, v___y_57335__boxed_3233_, v_____r_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_3235_, lean_object* v_e_3236_, uint8_t v_topLevel_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v_i_3255_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v_i_3276_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3295_; lean_object* v_a_3296_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___x_3337_; 
v___x_3337_ = l_Lean_Expr_isAtomic(v_e_3236_);
if (v___x_3337_ == 0)
{
uint8_t v_proofs_3338_; uint8_t v_types_3339_; uint8_t v_descend_3340_; lean_object* v___y_3342_; lean_object* v___y_3343_; uint8_t v___y_3360_; 
v_proofs_3338_ = lean_ctor_get_uint8(v_a_3238_, 0);
v_types_3339_ = lean_ctor_get_uint8(v_a_3238_, 1);
v_descend_3340_ = lean_ctor_get_uint8(v_a_3238_, 3);
if (v_descend_3340_ == 0)
{
goto v___jp_3383_;
}
else
{
if (v___x_3337_ == 0)
{
v___y_3360_ = v___x_3337_;
goto v___jp_3359_;
}
else
{
goto v___jp_3383_;
}
}
v___jp_3341_:
{
if (v_proofs_3338_ == 0)
{
lean_object* v___x_3344_; 
lean_inc_ref(v_e_3236_);
v___x_3344_ = l_Lean_Meta_isProof(v_e_3236_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; uint8_t v___x_3346_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = lean_unbox(v_a_3345_);
lean_dec(v_a_3345_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec_ref(v_e_3236_);
v___x_3347_ = lean_box(0);
lean_inc(v_a_3244_);
lean_inc_ref(v_a_3243_);
lean_inc(v_a_3242_);
lean_inc_ref(v_a_3241_);
lean_inc(v_a_3240_);
lean_inc(v_a_3239_);
lean_inc_ref(v_a_3238_);
v___x_3348_ = lean_apply_9(v___y_3343_, v___x_3347_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, lean_box(0));
v___y_3329_ = v___y_3342_;
v___y_3330_ = v___x_3348_;
goto v___jp_3328_;
}
else
{
lean_dec_ref(v___y_3343_);
v___y_3295_ = v___y_3342_;
v_a_3296_ = v_e_3236_;
goto v___jp_3294_;
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec_ref(v_e_3236_);
v_a_3349_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3344_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3344_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v_e_3236_);
v___x_3357_ = lean_box(0);
lean_inc(v_a_3244_);
lean_inc_ref(v_a_3243_);
lean_inc(v_a_3242_);
lean_inc_ref(v_a_3241_);
lean_inc(v_a_3240_);
lean_inc(v_a_3239_);
lean_inc_ref(v_a_3238_);
v___x_3358_ = lean_apply_9(v___y_3343_, v___x_3357_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, lean_box(0));
v___y_3329_ = v___y_3342_;
v___y_3330_ = v___x_3358_;
goto v___jp_3328_;
}
}
v___jp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3361_ = lean_st_ref_get(v_a_3239_);
v___x_3362_ = lean_box(v_topLevel_3237_);
lean_inc_ref(v_e_3236_);
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
lean_ctor_set(v___x_3363_, 1, v_e_3236_);
v___x_3364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___redArg(v___x_3361_, v___x_3363_);
lean_dec(v___x_3361_);
if (lean_obj_tag(v___x_3364_) == 0)
{
uint8_t v___x_3365_; 
v___x_3365_ = l_Lean_Meta_ExtractLets_containsLet(v_e_3236_);
if (v___x_3365_ == 0)
{
lean_dec(v_fvars_3235_);
v___y_3295_ = v___x_3363_;
v_a_3296_ = v_e_3236_;
goto v___jp_3294_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; lean_object* v___f_3372_; 
v___x_3366_ = lean_box(v_descend_3340_);
v___x_3367_ = lean_box(v___x_3365_);
v___x_3368_ = lean_box(v_topLevel_3237_);
v___x_3369_ = lean_box(v___y_3360_);
lean_inc_ref_n(v_e_3236_, 2);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3370_, 0, v___x_3366_);
lean_closure_set(v___f_3370_, 1, v_e_3236_);
lean_closure_set(v___f_3370_, 2, v_fvars_3235_);
lean_closure_set(v___f_3370_, 3, v___x_3367_);
lean_closure_set(v___f_3370_, 4, v___x_3368_);
lean_closure_set(v___f_3370_, 5, v___x_3369_);
v___x_3371_ = lean_box(v_types_3339_);
lean_inc_ref(v___f_3370_);
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3372_, 0, v___x_3371_);
lean_closure_set(v___f_3372_, 1, v_e_3236_);
lean_closure_set(v___f_3372_, 2, v___f_3370_);
if (v_topLevel_3237_ == 0)
{
lean_dec_ref(v___f_3370_);
v___y_3342_ = v___x_3363_;
v___y_3343_ = v___f_3372_;
goto v___jp_3341_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_Expr_isLet(v_e_3236_);
if (v___x_3373_ == 0)
{
uint8_t v___x_3374_; 
v___x_3374_ = l_Lean_Expr_isMData(v_e_3236_);
if (v___x_3374_ == 0)
{
lean_dec_ref(v___f_3370_);
v___y_3342_ = v___x_3363_;
v___y_3343_ = v___f_3372_;
goto v___jp_3341_;
}
else
{
lean_dec_ref(v___f_3372_);
lean_dec_ref(v_e_3236_);
v___y_3333_ = v___x_3363_;
v___y_3334_ = v___f_3370_;
goto v___jp_3332_;
}
}
else
{
lean_dec_ref(v___f_3372_);
lean_dec_ref(v_e_3236_);
v___y_3333_ = v___x_3363_;
v___y_3334_ = v___f_3370_;
goto v___jp_3332_;
}
}
}
}
else
{
lean_object* v_val_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref_known(v___x_3363_, 2);
lean_dec_ref(v_e_3236_);
lean_dec(v_fvars_3235_);
v_val_3375_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3364_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_val_3375_);
lean_dec(v___x_3364_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set_tag(v___x_3377_, 0);
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_val_3375_);
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
v___jp_3383_:
{
if (v_topLevel_3237_ == 0)
{
lean_object* v___x_3384_; 
lean_dec(v_fvars_3235_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_e_3236_);
return v___x_3384_;
}
else
{
if (v___x_3337_ == 0)
{
v___y_3360_ = v___x_3337_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3385_; 
lean_dec(v_fvars_3235_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v_e_3236_);
return v___x_3385_;
}
}
}
}
else
{
lean_object* v___x_3386_; 
lean_dec(v_fvars_3235_);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_e_3236_);
return v___x_3386_;
}
v___jp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_st_ref_put(v_a_3239_, v___y_3248_);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___y_3247_);
return v___x_3250_;
}
v___jp_3251_:
{
lean_object* v_size_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_size_3256_ = lean_ctor_get(v___y_3253_, 0);
v___x_3257_ = lean_unsigned_to_nat(1u);
v___x_3258_ = lean_nat_add(v_size_3256_, v___x_3257_);
lean_inc_ref(v___y_3254_);
v___x_3259_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3253_, v___x_3258_, v_i_3255_, v___y_3252_, v___y_3254_);
lean_dec(v_i_3255_);
v___y_3247_ = v___y_3254_;
v___y_3248_ = v___x_3259_;
goto v___jp_3246_;
}
v___jp_3260_:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___y_3263_, v___y_3261_);
switch(lean_obj_tag(v___x_3264_))
{
case 0:
{
lean_object* v_index_3265_; lean_object* v_size_3266_; lean_object* v___x_3267_; 
v_index_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_index_3265_);
lean_dec_ref_known(v___x_3264_, 3);
v_size_3266_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_size_3266_);
lean_inc_ref(v___y_3262_);
v___x_3267_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3263_, v_size_3266_, v_index_3265_, v___y_3261_, v___y_3262_);
lean_dec(v_index_3265_);
v___y_3247_ = v___y_3262_;
v___y_3248_ = v___x_3267_;
goto v___jp_3246_;
}
case 1:
{
lean_object* v_index_3268_; 
v_index_3268_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_index_3268_);
lean_dec_ref_known(v___x_3264_, 1);
v___y_3252_ = v___y_3261_;
v___y_3253_ = v___y_3263_;
v___y_3254_ = v___y_3262_;
v_i_3255_ = v_index_3268_;
goto v___jp_3251_;
}
default: 
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_unsigned_to_nat(0u);
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3263_, v___x_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_index_3271_; 
v_index_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_index_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___y_3252_ = v___y_3261_;
v___y_3253_ = v___y_3263_;
v___y_3254_ = v___y_3262_;
v_i_3255_ = v_index_3271_;
goto v___jp_3251_;
}
else
{
lean_dec_ref(v___y_3261_);
v___y_3247_ = v___y_3262_;
v___y_3248_ = v___y_3263_;
goto v___jp_3246_;
}
}
}
}
v___jp_3272_:
{
lean_object* v_size_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_size_3277_ = lean_ctor_get(v___y_3274_, 0);
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = lean_nat_add(v_size_3277_, v___x_3278_);
lean_inc_ref(v___y_3275_);
v___x_3280_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3274_, v___x_3279_, v_i_3276_, v___y_3273_, v___y_3275_);
lean_dec(v_i_3276_);
v___y_3247_ = v___y_3275_;
v___y_3248_ = v___x_3280_;
goto v___jp_3246_;
}
v___jp_3281_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___y_3284_);
lean_dec_ref(v___y_3284_);
v___x_3286_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3285_, v___y_3282_);
switch(lean_obj_tag(v___x_3286_))
{
case 0:
{
lean_object* v_index_3287_; lean_object* v_size_3288_; lean_object* v___x_3289_; 
v_index_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_index_3287_);
lean_dec_ref_known(v___x_3286_, 3);
v_size_3288_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_size_3288_);
lean_inc_ref(v___y_3283_);
v___x_3289_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3285_, v_size_3288_, v_index_3287_, v___y_3282_, v___y_3283_);
lean_dec(v_index_3287_);
v___y_3247_ = v___y_3283_;
v___y_3248_ = v___x_3289_;
goto v___jp_3246_;
}
case 1:
{
lean_object* v_index_3290_; 
v_index_3290_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_index_3290_);
lean_dec_ref_known(v___x_3286_, 1);
v___y_3273_ = v___y_3282_;
v___y_3274_ = v___x_3285_;
v___y_3275_ = v___y_3283_;
v_i_3276_ = v_index_3290_;
goto v___jp_3272_;
}
default: 
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3285_, v___x_3291_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_index_3293_; 
v_index_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_index_3293_);
lean_dec_ref_known(v___x_3292_, 1);
v___y_3273_ = v___y_3282_;
v___y_3274_ = v___x_3285_;
v___y_3275_ = v___y_3283_;
v_i_3276_ = v_index_3293_;
goto v___jp_3272_;
}
else
{
lean_dec_ref(v___y_3282_);
v___y_3247_ = v___y_3283_;
v___y_3248_ = v___x_3285_;
goto v___jp_3246_;
}
}
}
}
v___jp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_st_ref_take(v_a_3239_);
v___x_3298_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_3297_, v___y_3295_);
switch(lean_obj_tag(v___x_3298_))
{
case 0:
{
lean_object* v_index_3299_; lean_object* v_size_3300_; lean_object* v___x_3301_; 
v_index_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_index_3299_);
lean_dec_ref_known(v___x_3298_, 3);
v_size_3300_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_size_3300_);
lean_inc_ref(v_a_3296_);
v___x_3301_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3297_, v_size_3300_, v_index_3299_, v___y_3295_, v_a_3296_);
lean_dec(v_index_3299_);
v___y_3247_ = v_a_3296_;
v___y_3248_ = v___x_3301_;
goto v___jp_3246_;
}
case 1:
{
lean_object* v_index_3302_; lean_object* v_size_3303_; lean_object* v_keyArray_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
v_index_3302_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_index_3302_);
lean_dec_ref_known(v___x_3298_, 1);
v_size_3303_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_size_3303_);
v_keyArray_3304_ = lean_ctor_get(v___x_3297_, 1);
lean_inc_ref(v_keyArray_3304_);
v___x_3305_ = lean_unsigned_to_nat(1u);
v___x_3306_ = lean_nat_add(v_size_3303_, v___x_3305_);
lean_dec(v_size_3303_);
v___x_3307_ = lean_array_get_size(v_keyArray_3304_);
lean_dec_ref(v_keyArray_3304_);
v___x_3308_ = lean_nat_dec_lt(v___x_3306_, v___x_3307_);
if (v___x_3308_ == 0)
{
lean_dec(v___x_3306_);
lean_dec(v_index_3302_);
v___y_3282_ = v___y_3295_;
v___y_3283_ = v_a_3296_;
v___y_3284_ = v___x_3297_;
goto v___jp_3281_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3309_ = lean_unsigned_to_nat(4u);
v___x_3310_ = lean_nat_mul(v___x_3306_, v___x_3309_);
v___x_3311_ = lean_unsigned_to_nat(3u);
v___x_3312_ = lean_nat_mul(v___x_3307_, v___x_3311_);
v___x_3313_ = lean_nat_dec_le(v___x_3310_, v___x_3312_);
lean_dec(v___x_3312_);
lean_dec(v___x_3310_);
if (v___x_3313_ == 0)
{
lean_dec(v___x_3306_);
lean_dec(v_index_3302_);
v___y_3282_ = v___y_3295_;
v___y_3283_ = v_a_3296_;
v___y_3284_ = v___x_3297_;
goto v___jp_3281_;
}
else
{
lean_object* v___x_3314_; 
lean_inc_ref(v_a_3296_);
v___x_3314_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3297_, v___x_3306_, v_index_3302_, v___y_3295_, v_a_3296_);
lean_dec(v_index_3302_);
v___y_3247_ = v_a_3296_;
v___y_3248_ = v___x_3314_;
goto v___jp_3246_;
}
}
}
default: 
{
lean_object* v_size_3315_; lean_object* v_keyArray_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v_size_3315_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_size_3315_);
v_keyArray_3316_ = lean_ctor_get(v___x_3297_, 1);
lean_inc_ref(v_keyArray_3316_);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_nat_add(v_size_3315_, v___x_3317_);
lean_dec(v_size_3315_);
v___x_3319_ = lean_array_get_size(v_keyArray_3316_);
lean_dec_ref(v_keyArray_3316_);
v___x_3320_ = lean_nat_dec_lt(v___x_3318_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_dec(v___x_3318_);
v___x_3321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3297_);
lean_dec(v___x_3297_);
v___y_3261_ = v___y_3295_;
v___y_3262_ = v_a_3296_;
v___y_3263_ = v___x_3321_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3322_ = lean_unsigned_to_nat(4u);
v___x_3323_ = lean_nat_mul(v___x_3318_, v___x_3322_);
lean_dec(v___x_3318_);
v___x_3324_ = lean_unsigned_to_nat(3u);
v___x_3325_ = lean_nat_mul(v___x_3319_, v___x_3324_);
v___x_3326_ = lean_nat_dec_le(v___x_3323_, v___x_3325_);
lean_dec(v___x_3325_);
lean_dec(v___x_3323_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3297_);
lean_dec(v___x_3297_);
v___y_3261_ = v___y_3295_;
v___y_3262_ = v_a_3296_;
v___y_3263_ = v___x_3327_;
goto v___jp_3260_;
}
else
{
v___y_3261_ = v___y_3295_;
v___y_3262_ = v_a_3296_;
v___y_3263_ = v___x_3297_;
goto v___jp_3260_;
}
}
}
}
}
v___jp_3328_:
{
if (lean_obj_tag(v___y_3330_) == 0)
{
lean_object* v_a_3331_; 
v_a_3331_ = lean_ctor_get(v___y_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___y_3330_, 1);
v___y_3295_ = v___y_3329_;
v_a_3296_ = v_a_3331_;
goto v___jp_3294_;
}
else
{
lean_dec_ref(v___y_3329_);
return v___y_3330_;
}
}
v___jp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_box(0);
lean_inc(v_a_3244_);
lean_inc_ref(v_a_3243_);
lean_inc(v_a_3242_);
lean_inc_ref(v_a_3241_);
lean_inc(v_a_3240_);
lean_inc(v_a_3239_);
lean_inc_ref(v_a_3238_);
v___x_3336_ = lean_apply_9(v___y_3334_, v___x_3335_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, lean_box(0));
v___y_3329_ = v___y_3333_;
v___y_3330_ = v___x_3336_;
goto v___jp_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3387_, lean_object* v_struct_3388_, uint8_t v___y_3389_, lean_object* v_typeName_3390_, lean_object* v_idx_3391_, lean_object* v_e_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; 
lean_inc_ref(v_struct_3388_);
v___x_3401_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3387_, v_struct_3388_, v___y_3389_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3416_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3416_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3416_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
size_t v___x_3406_; size_t v___x_3407_; uint8_t v___x_3408_; 
v___x_3406_ = lean_ptr_addr(v_struct_3388_);
lean_dec_ref(v_struct_3388_);
v___x_3407_ = lean_ptr_addr(v_a_3402_);
v___x_3408_ = lean_usize_dec_eq(v___x_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
lean_dec_ref(v_e_3392_);
v___x_3409_ = l_Lean_Expr_proj___override(v_typeName_3390_, v_idx_3391_, v_a_3402_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3409_);
v___x_3411_ = v___x_3404_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
else
{
lean_object* v___x_3414_; 
lean_dec(v_a_3402_);
lean_dec(v_idx_3391_);
lean_dec(v_typeName_3390_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v_e_3392_);
v___x_3414_ = v___x_3404_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_e_3392_);
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
else
{
lean_dec_ref(v_e_3392_);
lean_dec(v_idx_3391_);
lean_dec(v_typeName_3390_);
lean_dec_ref(v_struct_3388_);
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__8___boxed(lean_object* v_fvars_3417_, lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_bs_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
size_t v_sz_boxed_3429_; size_t v_i_boxed_3430_; lean_object* v_res_3431_; 
v_sz_boxed_3429_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3430_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__8(v_fvars_3417_, v_sz_boxed_3429_, v_i_boxed_3430_, v_bs_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___redArg___boxed(lean_object* v_upperBound_3432_, lean_object* v_fst_3433_, lean_object* v_fvars_3434_, lean_object* v_a_3435_, lean_object* v_b_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___redArg(v_upperBound_3432_, v_fst_3433_, v_fvars_3434_, v_a_3435_, v_b_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec_ref(v_fst_3433_);
lean_dec(v_upperBound_3432_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3446_, lean_object* v_e_3447_, lean_object* v_isLet_3448_, lean_object* v_n_3449_, lean_object* v_t_3450_, lean_object* v_v_3451_, lean_object* v_b_3452_, lean_object* v_topLevel_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
uint8_t v_isLet_boxed_3462_; uint8_t v_topLevel_boxed_3463_; lean_object* v_res_3464_; 
v_isLet_boxed_3462_ = lean_unbox(v_isLet_3448_);
v_topLevel_boxed_3463_ = lean_unbox(v_topLevel_3453_);
v_res_3464_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3446_, v_e_3447_, v_isLet_boxed_3462_, v_n_3449_, v_t_3450_, v_v_3451_, v_b_3452_, v_topLevel_boxed_3463_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b1_3465_, lean_object* v_name_3466_, lean_object* v_type_3467_, lean_object* v_val_3468_, lean_object* v_k_3469_, uint8_t v_nondep_3470_, uint8_t v_kind_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_name_3466_, v_type_3467_, v_val_3468_, v_k_3469_, v_nondep_3470_, v_kind_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b1_3481_, lean_object* v_name_3482_, lean_object* v_type_3483_, lean_object* v_val_3484_, lean_object* v_k_3485_, lean_object* v_nondep_3486_, lean_object* v_kind_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
uint8_t v_nondep_boxed_3496_; uint8_t v_kind_boxed_3497_; lean_object* v_res_3498_; 
v_nondep_boxed_3496_ = lean_unbox(v_nondep_3486_);
v_kind_boxed_3497_ = lean_unbox(v_kind_3487_);
v_res_3498_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b1_3481_, v_name_3482_, v_type_3483_, v_val_3484_, v_k_3485_, v_nondep_boxed_3496_, v_kind_boxed_3497_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3499_, lean_object* v_m_3500_, lean_object* v_query_3501_){
_start:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3500_, v_query_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2___boxed(lean_object* v_00_u03b2_3503_, lean_object* v_m_3504_, lean_object* v_query_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2(v_00_u03b2_3503_, v_m_3504_, v_query_3505_);
lean_dec_ref(v_query_3505_);
lean_dec_ref(v_m_3504_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3507_, lean_object* v_m_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3510_, lean_object* v_m_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3510_, v_m_3511_);
lean_dec_ref(v_m_3511_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_00_u03b2_3513_, lean_object* v_m_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___redArg(v_m_3514_, v_a_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_00_u03b2_3517_, lean_object* v_m_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_00_u03b2_3517_, v_m_3518_, v_a_3519_);
lean_dec_ref(v_a_3519_);
lean_dec_ref(v_m_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_upperBound_3521_, lean_object* v_fst_3522_, lean_object* v_fvars_3523_, lean_object* v_inst_3524_, lean_object* v_R_3525_, lean_object* v_a_3526_, lean_object* v_b_3527_, lean_object* v_c_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___redArg(v_upperBound_3521_, v_fst_3522_, v_fvars_3523_, v_a_3526_, v_b_3527_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_upperBound_3538_, lean_object* v_fst_3539_, lean_object* v_fvars_3540_, lean_object* v_inst_3541_, lean_object* v_R_3542_, lean_object* v_a_3543_, lean_object* v_b_3544_, lean_object* v_c_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_upperBound_3538_, v_fst_3539_, v_fvars_3540_, v_inst_3541_, v_R_3542_, v_a_3543_, v_b_3544_, v_c_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec_ref(v_fst_3539_);
lean_dec(v_upperBound_3538_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12(lean_object* v_00_u03b2_3555_, lean_object* v_m_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___redArg(v_m_3556_, v_a_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12___boxed(lean_object* v_00_u03b2_3559_, lean_object* v_m_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12(v_00_u03b2_3559_, v_m_3560_, v_a_3561_);
lean_dec_ref(v_a_3561_);
lean_dec_ref(v_m_3560_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3563_, lean_object* v_m_3564_, lean_object* v_query_3565_, lean_object* v_x_3566_, lean_object* v_x_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_m_3564_, v_query_3565_, v_x_3566_, v_x_3567_, v_x_3568_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3571_, lean_object* v_m_3572_, lean_object* v_query_3573_, lean_object* v_x_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_, lean_object* v_x_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3571_, v_m_3572_, v_query_3573_, v_x_3574_, v_x_3575_, v_x_3576_, v_x_3577_);
lean_dec_ref(v_query_3573_);
lean_dec_ref(v_m_3572_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4(lean_object* v_00_u03b2_3579_, lean_object* v_init_3580_, lean_object* v_b_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___redArg(v_init_3580_, v_b_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3583_, lean_object* v_init_3584_, lean_object* v_b_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4(v_00_u03b2_3583_, v_init_3584_, v_b_3585_);
lean_dec_ref(v_b_3585_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6(lean_object* v_00_u03b2_3587_, lean_object* v_m_3588_, lean_object* v_query_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___redArg(v_m_3588_, v_query_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3591_, lean_object* v_m_3592_, lean_object* v_query_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__4_spec__6(v_00_u03b2_3591_, v_m_3592_, v_query_3593_);
lean_dec_ref(v_query_3593_);
lean_dec_ref(v_m_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15(lean_object* v_00_u03b2_3595_, lean_object* v_m_3596_, lean_object* v_query_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___redArg(v_m_3596_, v_query_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15___boxed(lean_object* v_00_u03b2_3599_, lean_object* v_m_3600_, lean_object* v_query_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__12_spec__15(v_00_u03b2_3599_, v_m_3600_, v_query_3601_);
lean_dec_ref(v_query_3601_);
lean_dec_ref(v_m_3600_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10(lean_object* v_00_u03b2_3603_, lean_object* v_b_3604_, lean_object* v_acc_3605_, lean_object* v_i_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___redArg(v_b_3604_, v_acc_3605_, v_i_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10___boxed(lean_object* v_00_u03b2_3608_, lean_object* v_b_3609_, lean_object* v_acc_3610_, lean_object* v_i_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__4_spec__10(v_00_u03b2_3608_, v_b_3609_, v_acc_3610_, v_i_3611_);
lean_dec_ref(v_b_3609_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v___x_3622_; lean_object* v_a_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; lean_object* v___x_3626_; 
v___x_3622_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3613_, v_a_3618_);
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3622_);
v___x_3624_ = lean_box(0);
v___x_3625_ = 1;
v___x_3626_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3624_, v_a_3623_, v___x_3625_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3637_, size_t v_i_3638_, lean_object* v_bs_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_usize_dec_lt(v_i_3638_, v_sz_3637_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3649_, 0, v_bs_3639_);
return v___x_3649_;
}
else
{
lean_object* v_v_3650_; lean_object* v___x_3651_; 
v_v_3650_ = lean_array_uget_borrowed(v_bs_3639_, v_i_3638_);
lean_inc(v_v_3650_);
v___x_3651_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3650_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v_bs_x27_3654_; size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = lean_unsigned_to_nat(0u);
v_bs_x27_3654_ = lean_array_uset(v_bs_3639_, v_i_3638_, v___x_3653_);
v___x_3655_ = ((size_t)1ULL);
v___x_3656_ = lean_usize_add(v_i_3638_, v___x_3655_);
v___x_3657_ = lean_array_uset(v_bs_x27_3654_, v_i_3638_, v_a_3652_);
v_i_3638_ = v___x_3656_;
v_bs_3639_ = v___x_3657_;
goto _start;
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref(v_bs_3639_);
v_a_3659_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3651_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3651_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3667_, lean_object* v_i_3668_, lean_object* v_bs_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
size_t v_sz_boxed_3678_; size_t v_i_boxed_3679_; lean_object* v_res_3680_; 
v_sz_boxed_3678_ = lean_unbox_usize(v_sz_3667_);
lean_dec(v_sz_3667_);
v_i_boxed_3679_ = lean_unbox_usize(v_i_3668_);
lean_dec(v_i_3668_);
v_res_3680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3678_, v_i_boxed_3679_, v_bs_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; uint8_t v_merge_3701_; 
v_merge_3701_ = lean_ctor_get_uint8(v_a_3682_, 6);
if (v_merge_3701_ == 0)
{
v___y_3691_ = v_a_3682_;
v___y_3692_ = v_a_3683_;
v___y_3693_ = v_a_3684_;
v___y_3694_ = v_a_3685_;
v___y_3695_ = v_a_3686_;
v___y_3696_ = v_a_3687_;
v___y_3697_ = v_a_3688_;
goto v___jp_3690_;
}
else
{
uint8_t v_useContext_3702_; 
v_useContext_3702_ = lean_ctor_get_uint8(v_a_3682_, 7);
if (v_useContext_3702_ == 0)
{
v___y_3691_ = v_a_3682_;
v___y_3692_ = v_a_3683_;
v___y_3693_ = v_a_3684_;
v___y_3694_ = v_a_3685_;
v___y_3695_ = v_a_3686_;
v___y_3696_ = v_a_3687_;
v___y_3697_ = v_a_3688_;
goto v___jp_3690_;
}
else
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_dec_ref_known(v___x_3703_, 1);
v___y_3691_ = v_a_3682_;
v___y_3692_ = v_a_3683_;
v___y_3693_ = v_a_3684_;
v___y_3694_ = v_a_3685_;
v___y_3695_ = v_a_3686_;
v___y_3696_ = v_a_3687_;
v___y_3697_ = v_a_3688_;
goto v___jp_3690_;
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_es_3681_);
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
v___jp_3690_:
{
size_t v_sz_3698_; size_t v___x_3699_; lean_object* v___x_3700_; 
v_sz_3698_ = lean_array_size(v_es_3681_);
v___x_3699_ = ((size_t)0ULL);
v___x_3700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3698_, v___x_3699_, v_es_3681_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
return v___x_3700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Meta_ExtractLets_extract(v_es_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
lean_dec(v_a_3719_);
lean_dec_ref(v_a_3718_);
lean_dec(v_a_3717_);
lean_dec_ref(v_a_3716_);
lean_dec(v_a_3715_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3722_, lean_object* v_x_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3722_, v_x_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
v_a_3738_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3729_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3729_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3746_, v_x_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3754_, lean_object* v_decls_3755_, lean_object* v_x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3755_, v_x_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3763_, lean_object* v_decls_3764_, lean_object* v_x_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3763_, v_decls_3764_, v_x_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3772_, size_t v_i_3773_, lean_object* v_bs_3774_){
_start:
{
uint8_t v___x_3775_; 
v___x_3775_ = lean_usize_dec_lt(v_i_3773_, v_sz_3772_);
if (v___x_3775_ == 0)
{
return v_bs_3774_;
}
else
{
lean_object* v_v_3776_; lean_object* v___x_3777_; lean_object* v_bs_x27_3778_; lean_object* v___x_3779_; size_t v___x_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
v_v_3776_ = lean_array_uget(v_bs_3774_, v_i_3773_);
v___x_3777_ = lean_unsigned_to_nat(0u);
v_bs_x27_3778_ = lean_array_uset(v_bs_3774_, v_i_3773_, v___x_3777_);
v___x_3779_ = l_Lean_LocalDecl_fvarId(v_v_3776_);
lean_dec(v_v_3776_);
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_add(v_i_3773_, v___x_3780_);
v___x_3782_ = lean_array_uset(v_bs_x27_3778_, v_i_3773_, v___x_3779_);
v_i_3773_ = v___x_3781_;
v_bs_3774_ = v___x_3782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3784_, lean_object* v_i_3785_, lean_object* v_bs_3786_){
_start:
{
size_t v_sz_boxed_3787_; size_t v_i_boxed_3788_; lean_object* v_res_3789_; 
v_sz_boxed_3787_ = lean_unbox_usize(v_sz_3784_);
lean_dec(v_sz_3784_);
v_i_boxed_3788_ = lean_unbox_usize(v_i_3785_);
lean_dec(v_i_3785_);
v_res_3789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3787_, v_i_boxed_3788_, v_bs_3786_);
return v_res_3789_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_3790_; lean_object* v___x_3791_; 
v_cellCount_3790_ = lean_unsigned_to_nat(16u);
v___x_3791_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3790_);
return v___x_3791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_3792_; lean_object* v___x_3793_; 
v_cellCount_3792_ = lean_unsigned_to_nat(16u);
v___x_3793_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3792_);
return v___x_3793_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3796_ = lean_unsigned_to_nat(0u);
v___x_3797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
lean_ctor_set(v___x_3797_, 1, v___x_3795_);
lean_ctor_set(v___x_3797_, 2, v___x_3794_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3798_, lean_object* v_givenNames_3799_, lean_object* v_k_3800_, lean_object* v_config_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2);
v___x_3808_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3809_, 0, v_givenNames_3799_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
lean_ctor_set(v___x_3809_, 2, v___x_3807_);
v___x_3810_ = lean_st_mk_ref(v___x_3809_);
v___x_3811_ = lean_st_mk_ref(v___x_3807_);
v___x_3812_ = l_Lean_Meta_ExtractLets_extract(v_es_3798_, v_config_3801_, v___x_3811_, v___x_3810_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v_givenNames_3816_; lean_object* v_decls_3817_; size_t v_sz_3818_; size_t v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; size_t v_sz_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v___x_3814_ = lean_st_ref_get(v___x_3811_);
lean_dec(v___x_3811_);
lean_dec(v___x_3814_);
v___x_3815_ = lean_st_ref_get(v___x_3810_);
lean_dec(v___x_3810_);
v_givenNames_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_givenNames_3816_);
v_decls_3817_ = lean_ctor_get(v___x_3815_, 1);
lean_inc_ref(v_decls_3817_);
lean_dec(v___x_3815_);
v_sz_3818_ = lean_array_size(v_decls_3817_);
v___x_3819_ = ((size_t)0ULL);
v___x_3820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_3818_, v___x_3819_, v_decls_3817_);
lean_inc_ref(v___x_3820_);
v___x_3821_ = lean_array_to_list(v___x_3820_);
v_sz_3822_ = lean_array_size(v___x_3820_);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3822_, v___x_3819_, v___x_3820_);
v___x_3824_ = lean_apply_3(v_k_3800_, v___x_3823_, v_a_3813_, v_givenNames_3816_);
v___x_3825_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3821_, v___x_3824_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_);
return v___x_3825_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v___x_3811_);
lean_dec(v___x_3810_);
lean_dec_ref(v_k_3800_);
v_a_3826_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3812_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3812_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3834_, lean_object* v_givenNames_3835_, lean_object* v_k_3836_, lean_object* v_config_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3834_, v_givenNames_3835_, v_k_3836_, v_config_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec_ref(v_config_3837_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3844_, lean_object* v_es_3845_, lean_object* v_givenNames_3846_, lean_object* v_k_3847_, lean_object* v_config_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3845_, v_givenNames_3846_, v_k_3847_, v_config_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3855_, lean_object* v_es_3856_, lean_object* v_givenNames_3857_, lean_object* v_k_3858_, lean_object* v_config_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3855_, v_es_3856_, v_givenNames_3857_, v_k_3858_, v_config_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec_ref(v_config_3859_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3866_, lean_object* v_runInBase_3867_, lean_object* v_b_3868_, lean_object* v_c_3869_, lean_object* v_d_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_apply_3(v_k_3866_, v_b_3868_, v_c_3869_, v_d_3870_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3873_);
lean_inc(v___y_3872_);
lean_inc_ref(v___y_3871_);
v___x_3877_ = lean_apply_7(v_runInBase_3867_, lean_box(0), v___x_3876_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, lean_box(0));
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3878_, lean_object* v_runInBase_3879_, lean_object* v_b_3880_, lean_object* v_c_3881_, lean_object* v_d_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3878_, v_runInBase_3879_, v_b_3880_, v_c_3881_, v_d_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3889_, lean_object* v_es_3890_, lean_object* v_givenNames_3891_, lean_object* v_config_3892_, lean_object* v_runInBase_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___f_3899_; lean_object* v___x_3900_; 
v___f_3899_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3899_, 0, v_k_3889_);
lean_closure_set(v___f_3899_, 1, v_runInBase_3893_);
v___x_3900_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3890_, v_givenNames_3891_, v___f_3899_, v_config_3892_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3901_, lean_object* v_es_3902_, lean_object* v_givenNames_3903_, lean_object* v_config_3904_, lean_object* v_runInBase_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3901_, v_es_3902_, v_givenNames_3903_, v_config_3904_, v_runInBase_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec_ref(v_config_3904_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3912_, lean_object* v_inst_3913_, lean_object* v_es_3914_, lean_object* v_givenNames_3915_, lean_object* v_k_3916_, lean_object* v_config_3917_){
_start:
{
lean_object* v_toBind_3918_; lean_object* v_liftWith_3919_; lean_object* v_restoreM_3920_; lean_object* v___f_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_toBind_3918_ = lean_ctor_get(v_inst_3912_, 1);
lean_inc(v_toBind_3918_);
lean_dec_ref(v_inst_3912_);
v_liftWith_3919_ = lean_ctor_get(v_inst_3913_, 0);
lean_inc(v_liftWith_3919_);
v_restoreM_3920_ = lean_ctor_get(v_inst_3913_, 1);
lean_inc(v_restoreM_3920_);
lean_dec_ref(v_inst_3913_);
v___f_3921_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3921_, 0, v_k_3916_);
lean_closure_set(v___f_3921_, 1, v_es_3914_);
lean_closure_set(v___f_3921_, 2, v_givenNames_3915_);
lean_closure_set(v___f_3921_, 3, v_config_3917_);
v___x_3922_ = lean_apply_2(v_liftWith_3919_, lean_box(0), v___f_3921_);
v___x_3923_ = lean_apply_1(v_restoreM_3920_, lean_box(0));
v___x_3924_ = lean_apply_4(v_toBind_3918_, lean_box(0), lean_box(0), v___x_3922_, v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3925_, lean_object* v_00_u03b1_3926_, lean_object* v_inst_3927_, lean_object* v_inst_3928_, lean_object* v_es_3929_, lean_object* v_givenNames_3930_, lean_object* v_k_3931_, lean_object* v_config_3932_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_Meta_extractLets___redArg(v_inst_3927_, v_inst_3928_, v_es_3929_, v_givenNames_3930_, v_k_3931_, v_config_3932_);
return v___x_3933_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2);
v___x_3935_ = ((lean_object*)(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0));
v___x_3936_ = lean_box(0);
v___x_3937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set(v___x_3937_, 1, v___x_3935_);
lean_ctor_set(v___x_3937_, 2, v___x_3934_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3938_, lean_object* v_config_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; uint8_t v_proofs_3950_; uint8_t v_types_3951_; uint8_t v_implicits_3952_; uint8_t v_descend_3953_; uint8_t v_underBinder_3954_; uint8_t v_usedOnly_3955_; uint8_t v_merge_3956_; uint8_t v_useContext_3957_; uint8_t v_preserveBinderNames_3958_; uint8_t v_lift_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3993_; 
v___x_3945_ = lean_unsigned_to_nat(0u);
v___x_3946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__2);
v___x_3947_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3948_ = lean_st_mk_ref(v___x_3947_);
v___x_3949_ = lean_st_mk_ref(v___x_3946_);
v_proofs_3950_ = lean_ctor_get_uint8(v_config_3939_, 0);
v_types_3951_ = lean_ctor_get_uint8(v_config_3939_, 1);
v_implicits_3952_ = lean_ctor_get_uint8(v_config_3939_, 2);
v_descend_3953_ = lean_ctor_get_uint8(v_config_3939_, 3);
v_underBinder_3954_ = lean_ctor_get_uint8(v_config_3939_, 4);
v_usedOnly_3955_ = lean_ctor_get_uint8(v_config_3939_, 5);
v_merge_3956_ = lean_ctor_get_uint8(v_config_3939_, 6);
v_useContext_3957_ = lean_ctor_get_uint8(v_config_3939_, 7);
v_preserveBinderNames_3958_ = lean_ctor_get_uint8(v_config_3939_, 9);
v_lift_3959_ = lean_ctor_get_uint8(v_config_3939_, 10);
v_isSharedCheck_3993_ = !lean_is_exclusive(v_config_3939_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3961_ = v_config_3939_;
v_isShared_3962_ = v_isSharedCheck_3993_;
goto v_resetjp_3960_;
}
else
{
lean_dec(v_config_3939_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3993_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; lean_object* v___x_3968_; 
v___x_3963_ = lean_unsigned_to_nat(1u);
v___x_3964_ = lean_mk_empty_array_with_capacity(v___x_3963_);
v___x_3965_ = lean_array_push(v___x_3964_, v_e_3938_);
v___x_3966_ = 1;
if (v_isShared_3962_ == 0)
{
v___x_3968_ = v___x_3961_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 0, v_proofs_3950_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 1, v_types_3951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 2, v_implicits_3952_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 3, v_descend_3953_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 4, v_underBinder_3954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 5, v_usedOnly_3955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 6, v_merge_3956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 7, v_useContext_3957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 9, v_preserveBinderNames_3958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, 10, v_lift_3959_);
v___x_3968_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3969_; 
lean_ctor_set_uint8(v___x_3968_, 8, v___x_3966_);
v___x_3969_ = l_Lean_Meta_ExtractLets_extract(v___x_3965_, v___x_3968_, v___x_3949_, v___x_3948_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
lean_dec_ref(v___x_3968_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3983_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3983_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3983_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v_decls_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3974_ = lean_st_ref_get(v___x_3949_);
lean_dec(v___x_3949_);
lean_dec(v___x_3974_);
v___x_3975_ = lean_st_ref_get(v___x_3948_);
lean_dec(v___x_3948_);
v_decls_3976_ = lean_ctor_get(v___x_3975_, 1);
lean_inc_ref(v_decls_3976_);
lean_dec(v___x_3975_);
v___x_3977_ = l_Lean_instInhabitedExpr;
v___x_3978_ = lean_array_get(v___x_3977_, v_a_3970_, v___x_3945_);
lean_dec(v_a_3970_);
v___x_3979_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3976_, v___x_3978_);
lean_dec_ref(v_decls_3976_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3979_);
v___x_3981_ = v___x_3972_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v___x_3949_);
lean_dec(v___x_3948_);
v_a_3984_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3969_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3969_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3994_, lean_object* v_config_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_Meta_liftLets(v_e_3994_, v_config_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
return v_res_4001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_4004_ = l_Lean_stringToMessageData(v___x_4003_);
return v___x_4004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_4007_, lean_object* v_mvarId_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_4015_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_4007_, v_mvarId_4008_, v___x_4014_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_4016_, lean_object* v_mvarId_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_4016_, v_mvarId_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_4024_, lean_object* v_tactic_4025_, lean_object* v_mvarId_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_4025_, v_mvarId_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_4033_, lean_object* v_tactic_4034_, lean_object* v_mvarId_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_4033_, v_tactic_4034_, v_mvarId_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_4042_, lean_object* v_b_4043_, lean_object* v_c_4044_, lean_object* v_d_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v___x_4051_; 
lean_inc(v___y_4049_);
lean_inc_ref(v___y_4048_);
lean_inc(v___y_4047_);
lean_inc_ref(v___y_4046_);
v___x_4051_ = lean_apply_8(v_k_4042_, v_b_4043_, v_c_4044_, v_d_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, lean_box(0));
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_4052_, lean_object* v_b_4053_, lean_object* v_c_4054_, lean_object* v_d_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_4052_, v_b_4053_, v_c_4054_, v_d_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_4062_, lean_object* v_givenNames_4063_, lean_object* v_k_4064_, lean_object* v_config_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___f_4071_; lean_object* v___x_4072_; 
v___f_4071_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4071_, 0, v_k_4064_);
v___x_4072_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_4062_, v_givenNames_4063_, v___f_4071_, v_config_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
v_a_4081_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4072_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4072_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_4089_, lean_object* v_givenNames_4090_, lean_object* v_k_4091_, lean_object* v_config_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_4089_, v_givenNames_4090_, v_k_4091_, v_config_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec_ref(v_config_4092_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_4099_, lean_object* v_es_4100_, lean_object* v_givenNames_4101_, lean_object* v_k_4102_, lean_object* v_config_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_4100_, v_givenNames_4101_, v_k_4102_, v_config_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_4110_, lean_object* v_es_4111_, lean_object* v_givenNames_4112_, lean_object* v_k_4113_, lean_object* v_config_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_4110_, v_es_4111_, v_givenNames_4112_, v_k_4113_, v_config_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec_ref(v_config_4114_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_4121_, lean_object* v_x_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4121_, v_x_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4128_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
v_a_4137_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4128_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4128_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_4145_, lean_object* v_x_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4145_, v_x_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_4153_, lean_object* v_mvarId_4154_, lean_object* v_x_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4154_, v_x_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_4162_, lean_object* v_mvarId_4163_, lean_object* v_x_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_4162_, v_mvarId_4163_, v_x_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_4171_, lean_object* v_x_4172_, lean_object* v_x_4173_, lean_object* v_x_4174_){
_start:
{
lean_object* v_ks_4175_; lean_object* v_vs_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4200_; 
v_ks_4175_ = lean_ctor_get(v_x_4171_, 0);
v_vs_4176_ = lean_ctor_get(v_x_4171_, 1);
v_isSharedCheck_4200_ = !lean_is_exclusive(v_x_4171_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4178_ = v_x_4171_;
v_isShared_4179_ = v_isSharedCheck_4200_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_vs_4176_);
lean_inc(v_ks_4175_);
lean_dec(v_x_4171_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4200_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; uint8_t v___x_4181_; 
v___x_4180_ = lean_array_get_size(v_ks_4175_);
v___x_4181_ = lean_nat_dec_lt(v_x_4172_, v___x_4180_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4185_; 
lean_dec(v_x_4172_);
v___x_4182_ = lean_array_push(v_ks_4175_, v_x_4173_);
v___x_4183_ = lean_array_push(v_vs_4176_, v_x_4174_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 1, v___x_4183_);
lean_ctor_set(v___x_4178_, 0, v___x_4182_);
v___x_4185_ = v___x_4178_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4182_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___x_4183_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
else
{
lean_object* v_k_x27_4187_; uint8_t v___x_4188_; 
v_k_x27_4187_ = lean_array_fget_borrowed(v_ks_4175_, v_x_4172_);
v___x_4188_ = l_Lean_instBEqMVarId_beq(v_x_4173_, v_k_x27_4187_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4190_; 
if (v_isShared_4179_ == 0)
{
v___x_4190_ = v___x_4178_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_ks_4175_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_vs_4176_);
v___x_4190_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = lean_unsigned_to_nat(1u);
v___x_4192_ = lean_nat_add(v_x_4172_, v___x_4191_);
lean_dec(v_x_4172_);
v_x_4171_ = v___x_4190_;
v_x_4172_ = v___x_4192_;
goto _start;
}
}
else
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4195_ = lean_array_fset(v_ks_4175_, v_x_4172_, v_x_4173_);
v___x_4196_ = lean_array_fset(v_vs_4176_, v_x_4172_, v_x_4174_);
lean_dec(v_x_4172_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 1, v___x_4196_);
lean_ctor_set(v___x_4178_, 0, v___x_4195_);
v___x_4198_ = v___x_4178_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4195_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_4201_, lean_object* v_k_4202_, lean_object* v_v_4203_){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = lean_unsigned_to_nat(0u);
v___x_4205_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_4201_, v___x_4204_, v_k_4202_, v_v_4203_);
return v___x_4205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_4207_, size_t v_x_4208_, size_t v_x_4209_, lean_object* v_x_4210_, lean_object* v_x_4211_){
_start:
{
if (lean_obj_tag(v_x_4207_) == 0)
{
lean_object* v_es_4212_; size_t v___x_4213_; size_t v___x_4214_; lean_object* v_j_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; 
v_es_4212_ = lean_ctor_get(v_x_4207_, 0);
v___x_4213_ = ((size_t)31ULL);
v___x_4214_ = lean_usize_land(v_x_4208_, v___x_4213_);
v_j_4215_ = lean_usize_to_nat(v___x_4214_);
v___x_4216_ = lean_array_get_size(v_es_4212_);
v___x_4217_ = lean_nat_dec_lt(v_j_4215_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_dec(v_j_4215_);
lean_dec(v_x_4211_);
lean_dec(v_x_4210_);
return v_x_4207_;
}
else
{
lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4256_; 
lean_inc_ref(v_es_4212_);
v_isSharedCheck_4256_ = !lean_is_exclusive(v_x_4207_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; 
v_unused_4257_ = lean_ctor_get(v_x_4207_, 0);
lean_dec(v_unused_4257_);
v___x_4219_ = v_x_4207_;
v_isShared_4220_ = v_isSharedCheck_4256_;
goto v_resetjp_4218_;
}
else
{
lean_dec(v_x_4207_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4256_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v_v_4221_; lean_object* v___x_4222_; lean_object* v_xs_x27_4223_; lean_object* v___y_4225_; 
v_v_4221_ = lean_array_fget(v_es_4212_, v_j_4215_);
v___x_4222_ = lean_box(0);
v_xs_x27_4223_ = lean_array_fset(v_es_4212_, v_j_4215_, v___x_4222_);
switch(lean_obj_tag(v_v_4221_))
{
case 0:
{
lean_object* v_key_4230_; lean_object* v_val_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4241_; 
v_key_4230_ = lean_ctor_get(v_v_4221_, 0);
v_val_4231_ = lean_ctor_get(v_v_4221_, 1);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_v_4221_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4233_ = v_v_4221_;
v_isShared_4234_ = v_isSharedCheck_4241_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_val_4231_);
lean_inc(v_key_4230_);
lean_dec(v_v_4221_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4241_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
uint8_t v___x_4235_; 
v___x_4235_ = l_Lean_instBEqMVarId_beq(v_x_4210_, v_key_4230_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_del_object(v___x_4233_);
v___x_4236_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4230_, v_val_4231_, v_x_4210_, v_x_4211_);
v___x_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4236_);
v___y_4225_ = v___x_4237_;
goto v___jp_4224_;
}
else
{
lean_object* v___x_4239_; 
lean_dec(v_val_4231_);
lean_dec(v_key_4230_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v_x_4211_);
lean_ctor_set(v___x_4233_, 0, v_x_4210_);
v___x_4239_ = v___x_4233_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_x_4210_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_x_4211_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
v___y_4225_ = v___x_4239_;
goto v___jp_4224_;
}
}
}
}
case 1:
{
lean_object* v_node_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4254_; 
v_node_4242_ = lean_ctor_get(v_v_4221_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_v_4221_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4244_ = v_v_4221_;
v_isShared_4245_ = v_isSharedCheck_4254_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_node_4242_);
lean_dec(v_v_4221_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4254_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
size_t v___x_4246_; size_t v___x_4247_; size_t v___x_4248_; size_t v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4252_; 
v___x_4246_ = ((size_t)5ULL);
v___x_4247_ = lean_usize_shift_right(v_x_4208_, v___x_4246_);
v___x_4248_ = ((size_t)1ULL);
v___x_4249_ = lean_usize_add(v_x_4209_, v___x_4248_);
v___x_4250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_4242_, v___x_4247_, v___x_4249_, v_x_4210_, v_x_4211_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4250_);
v___x_4252_ = v___x_4244_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
v___y_4225_ = v___x_4252_;
goto v___jp_4224_;
}
}
}
default: 
{
lean_object* v___x_4255_; 
v___x_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4255_, 0, v_x_4210_);
lean_ctor_set(v___x_4255_, 1, v_x_4211_);
v___y_4225_ = v___x_4255_;
goto v___jp_4224_;
}
}
v___jp_4224_:
{
lean_object* v___x_4226_; lean_object* v___x_4228_; 
v___x_4226_ = lean_array_fset(v_xs_x27_4223_, v_j_4215_, v___y_4225_);
lean_dec(v_j_4215_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4226_);
v___x_4228_ = v___x_4219_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4226_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
else
{
lean_object* v_ks_4258_; lean_object* v_vs_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4279_; 
v_ks_4258_ = lean_ctor_get(v_x_4207_, 0);
v_vs_4259_ = lean_ctor_get(v_x_4207_, 1);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_x_4207_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4261_ = v_x_4207_;
v_isShared_4262_ = v_isSharedCheck_4279_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_vs_4259_);
lean_inc(v_ks_4258_);
lean_dec(v_x_4207_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4279_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_ks_4258_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_vs_4259_);
v___x_4264_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
lean_object* v_newNode_4265_; uint8_t v___y_4267_; size_t v___x_4273_; uint8_t v___x_4274_; 
v_newNode_4265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_4264_, v_x_4210_, v_x_4211_);
v___x_4273_ = ((size_t)7ULL);
v___x_4274_ = lean_usize_dec_le(v___x_4273_, v_x_4209_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; 
v___x_4275_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4265_);
v___x_4276_ = lean_unsigned_to_nat(4u);
v___x_4277_ = lean_nat_dec_lt(v___x_4275_, v___x_4276_);
lean_dec(v___x_4275_);
v___y_4267_ = v___x_4277_;
goto v___jp_4266_;
}
else
{
v___y_4267_ = v___x_4274_;
goto v___jp_4266_;
}
v___jp_4266_:
{
if (v___y_4267_ == 0)
{
lean_object* v_ks_4268_; lean_object* v_vs_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v_ks_4268_ = lean_ctor_get(v_newNode_4265_, 0);
lean_inc_ref(v_ks_4268_);
v_vs_4269_ = lean_ctor_get(v_newNode_4265_, 1);
lean_inc_ref(v_vs_4269_);
lean_dec_ref(v_newNode_4265_);
v___x_4270_ = lean_unsigned_to_nat(0u);
v___x_4271_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_4272_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_4209_, v_ks_4268_, v_vs_4269_, v___x_4270_, v___x_4271_);
lean_dec_ref(v_vs_4269_);
lean_dec_ref(v_ks_4268_);
return v___x_4272_;
}
else
{
return v_newNode_4265_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_4280_, lean_object* v_keys_4281_, lean_object* v_vals_4282_, lean_object* v_i_4283_, lean_object* v_entries_4284_){
_start:
{
lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4285_ = lean_array_get_size(v_keys_4281_);
v___x_4286_ = lean_nat_dec_lt(v_i_4283_, v___x_4285_);
if (v___x_4286_ == 0)
{
lean_dec(v_i_4283_);
return v_entries_4284_;
}
else
{
lean_object* v_k_4287_; lean_object* v_v_4288_; uint64_t v___x_4289_; size_t v_h_4290_; size_t v___x_4291_; lean_object* v___x_4292_; size_t v___x_4293_; size_t v___x_4294_; size_t v___x_4295_; size_t v_h_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v_k_4287_ = lean_array_fget_borrowed(v_keys_4281_, v_i_4283_);
v_v_4288_ = lean_array_fget_borrowed(v_vals_4282_, v_i_4283_);
v___x_4289_ = l_Lean_instHashableMVarId_hash(v_k_4287_);
v_h_4290_ = lean_uint64_to_usize(v___x_4289_);
v___x_4291_ = ((size_t)5ULL);
v___x_4292_ = lean_unsigned_to_nat(1u);
v___x_4293_ = ((size_t)1ULL);
v___x_4294_ = lean_usize_sub(v_depth_4280_, v___x_4293_);
v___x_4295_ = lean_usize_mul(v___x_4291_, v___x_4294_);
v_h_4296_ = lean_usize_shift_right(v_h_4290_, v___x_4295_);
v___x_4297_ = lean_nat_add(v_i_4283_, v___x_4292_);
lean_dec(v_i_4283_);
lean_inc(v_v_4288_);
lean_inc(v_k_4287_);
v___x_4298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_4284_, v_h_4296_, v_depth_4280_, v_k_4287_, v_v_4288_);
v_i_4283_ = v___x_4297_;
v_entries_4284_ = v___x_4298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_4300_, lean_object* v_keys_4301_, lean_object* v_vals_4302_, lean_object* v_i_4303_, lean_object* v_entries_4304_){
_start:
{
size_t v_depth_boxed_4305_; lean_object* v_res_4306_; 
v_depth_boxed_4305_ = lean_unbox_usize(v_depth_4300_);
lean_dec(v_depth_4300_);
v_res_4306_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_4305_, v_keys_4301_, v_vals_4302_, v_i_4303_, v_entries_4304_);
lean_dec_ref(v_vals_4302_);
lean_dec_ref(v_keys_4301_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_4307_, lean_object* v_x_4308_, lean_object* v_x_4309_, lean_object* v_x_4310_, lean_object* v_x_4311_){
_start:
{
size_t v_x_2314__boxed_4312_; size_t v_x_2315__boxed_4313_; lean_object* v_res_4314_; 
v_x_2314__boxed_4312_ = lean_unbox_usize(v_x_4308_);
lean_dec(v_x_4308_);
v_x_2315__boxed_4313_ = lean_unbox_usize(v_x_4309_);
lean_dec(v_x_4309_);
v_res_4314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4307_, v_x_2314__boxed_4312_, v_x_2315__boxed_4313_, v_x_4310_, v_x_4311_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_4315_, lean_object* v_x_4316_, lean_object* v_x_4317_){
_start:
{
uint64_t v___x_4318_; size_t v___x_4319_; size_t v___x_4320_; lean_object* v___x_4321_; 
v___x_4318_ = l_Lean_instHashableMVarId_hash(v_x_4316_);
v___x_4319_ = lean_uint64_to_usize(v___x_4318_);
v___x_4320_ = ((size_t)1ULL);
v___x_4321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4315_, v___x_4319_, v___x_4320_, v_x_4316_, v_x_4317_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_4322_, lean_object* v_val_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; lean_object* v_mctx_4327_; lean_object* v_cache_4328_; lean_object* v_zetaDeltaFVarIds_4329_; lean_object* v_postponed_4330_; lean_object* v_diag_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4360_; 
v___x_4326_ = lean_st_ref_take(v___y_4324_);
v_mctx_4327_ = lean_ctor_get(v___x_4326_, 0);
v_cache_4328_ = lean_ctor_get(v___x_4326_, 1);
v_zetaDeltaFVarIds_4329_ = lean_ctor_get(v___x_4326_, 2);
v_postponed_4330_ = lean_ctor_get(v___x_4326_, 3);
v_diag_4331_ = lean_ctor_get(v___x_4326_, 4);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4333_ = v___x_4326_;
v_isShared_4334_ = v_isSharedCheck_4360_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_diag_4331_);
lean_inc(v_postponed_4330_);
lean_inc(v_zetaDeltaFVarIds_4329_);
lean_inc(v_cache_4328_);
lean_inc(v_mctx_4327_);
lean_dec(v___x_4326_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4360_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v_depth_4335_; lean_object* v_levelAssignDepth_4336_; lean_object* v_lmvarCounter_4337_; lean_object* v_mvarCounter_4338_; lean_object* v_lDecls_4339_; lean_object* v_decls_4340_; lean_object* v_userNames_4341_; lean_object* v_lAssignment_4342_; lean_object* v_eAssignment_4343_; lean_object* v_dAssignment_4344_; lean_object* v_instanceTypedMVars_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4359_; 
v_depth_4335_ = lean_ctor_get(v_mctx_4327_, 0);
v_levelAssignDepth_4336_ = lean_ctor_get(v_mctx_4327_, 1);
v_lmvarCounter_4337_ = lean_ctor_get(v_mctx_4327_, 2);
v_mvarCounter_4338_ = lean_ctor_get(v_mctx_4327_, 3);
v_lDecls_4339_ = lean_ctor_get(v_mctx_4327_, 4);
v_decls_4340_ = lean_ctor_get(v_mctx_4327_, 5);
v_userNames_4341_ = lean_ctor_get(v_mctx_4327_, 6);
v_lAssignment_4342_ = lean_ctor_get(v_mctx_4327_, 7);
v_eAssignment_4343_ = lean_ctor_get(v_mctx_4327_, 8);
v_dAssignment_4344_ = lean_ctor_get(v_mctx_4327_, 9);
v_instanceTypedMVars_4345_ = lean_ctor_get(v_mctx_4327_, 10);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_mctx_4327_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4347_ = v_mctx_4327_;
v_isShared_4348_ = v_isSharedCheck_4359_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_instanceTypedMVars_4345_);
lean_inc(v_dAssignment_4344_);
lean_inc(v_eAssignment_4343_);
lean_inc(v_lAssignment_4342_);
lean_inc(v_userNames_4341_);
lean_inc(v_decls_4340_);
lean_inc(v_lDecls_4339_);
lean_inc(v_mvarCounter_4338_);
lean_inc(v_lmvarCounter_4337_);
lean_inc(v_levelAssignDepth_4336_);
lean_inc(v_depth_4335_);
lean_dec(v_mctx_4327_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4359_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4349_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_4343_, v_mvarId_4322_, v_val_4323_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 8, v___x_4349_);
v___x_4351_ = v___x_4347_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_depth_4335_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v_levelAssignDepth_4336_);
lean_ctor_set(v_reuseFailAlloc_4358_, 2, v_lmvarCounter_4337_);
lean_ctor_set(v_reuseFailAlloc_4358_, 3, v_mvarCounter_4338_);
lean_ctor_set(v_reuseFailAlloc_4358_, 4, v_lDecls_4339_);
lean_ctor_set(v_reuseFailAlloc_4358_, 5, v_decls_4340_);
lean_ctor_set(v_reuseFailAlloc_4358_, 6, v_userNames_4341_);
lean_ctor_set(v_reuseFailAlloc_4358_, 7, v_lAssignment_4342_);
lean_ctor_set(v_reuseFailAlloc_4358_, 8, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4358_, 9, v_dAssignment_4344_);
lean_ctor_set(v_reuseFailAlloc_4358_, 10, v_instanceTypedMVars_4345_);
v___x_4351_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4353_; 
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v___x_4351_);
v___x_4353_ = v___x_4333_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4351_);
lean_ctor_set(v_reuseFailAlloc_4357_, 1, v_cache_4328_);
lean_ctor_set(v_reuseFailAlloc_4357_, 2, v_zetaDeltaFVarIds_4329_);
lean_ctor_set(v_reuseFailAlloc_4357_, 3, v_postponed_4330_);
lean_ctor_set(v_reuseFailAlloc_4357_, 4, v_diag_4331_);
v___x_4353_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4354_ = lean_st_ref_put(v___y_4324_, v___x_4353_);
v___x_4355_ = lean_box(0);
v___x_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4355_);
return v___x_4356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4361_, lean_object* v_val_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4361_, v_val_4362_, v___y_4363_);
lean_dec(v___y_4363_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4366_, size_t v_i_4367_, lean_object* v_bs_4368_){
_start:
{
uint8_t v___x_4369_; 
v___x_4369_ = lean_usize_dec_lt(v_i_4367_, v_sz_4366_);
if (v___x_4369_ == 0)
{
return v_bs_4368_;
}
else
{
lean_object* v_v_4370_; lean_object* v___x_4371_; lean_object* v_bs_x27_4372_; lean_object* v___x_4373_; size_t v___x_4374_; size_t v___x_4375_; lean_object* v___x_4376_; 
v_v_4370_ = lean_array_uget(v_bs_4368_, v_i_4367_);
v___x_4371_ = lean_unsigned_to_nat(0u);
v_bs_x27_4372_ = lean_array_uset(v_bs_4368_, v_i_4367_, v___x_4371_);
v___x_4373_ = l_Lean_Expr_fvar___override(v_v_4370_);
v___x_4374_ = ((size_t)1ULL);
v___x_4375_ = lean_usize_add(v_i_4367_, v___x_4374_);
v___x_4376_ = lean_array_uset(v_bs_x27_4372_, v_i_4367_, v___x_4373_);
v_i_4367_ = v___x_4375_;
v_bs_4368_ = v___x_4376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4378_, lean_object* v_i_4379_, lean_object* v_bs_4380_){
_start:
{
size_t v_sz_boxed_4381_; size_t v_i_boxed_4382_; lean_object* v_res_4383_; 
v_sz_boxed_4381_ = lean_unbox_usize(v_sz_4378_);
lean_dec(v_sz_4378_);
v_i_boxed_4382_ = lean_unbox_usize(v_i_4379_);
lean_dec(v_i_4379_);
v_res_4383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4381_, v_i_boxed_4382_, v_bs_4380_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4384_, lean_object* v_mvarId_4385_, lean_object* v___x_4386_, lean_object* v_a_4387_, lean_object* v_fvarIds_4388_, lean_object* v_es_4389_, lean_object* v_givenNames_x27_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___y_4448_; lean_object* v___x_4458_; uint8_t v___x_4459_; 
v___x_4396_ = lean_unsigned_to_nat(0u);
v___x_4397_ = lean_array_get_borrowed(v___x_4384_, v_es_4389_, v___x_4396_);
v___x_4458_ = lean_array_get_size(v_fvarIds_4388_);
v___x_4459_ = lean_nat_dec_eq(v___x_4458_, v___x_4396_);
if (v___x_4459_ == 0)
{
v___y_4448_ = v___x_4459_;
goto v___jp_4447_;
}
else
{
uint8_t v___x_4460_; 
v___x_4460_ = lean_expr_eqv(v_a_4387_, v___x_4397_);
v___y_4448_ = v___x_4460_;
goto v___jp_4447_;
}
v___jp_4398_:
{
lean_object* v___x_4399_; 
lean_inc(v_mvarId_4385_);
v___x_4399_ = l_Lean_MVarId_getTag(v_mvarId_4385_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
lean_inc(v___x_4397_);
v___x_4401_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4397_, v_a_4400_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; size_t v_sz_4403_; size_t v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; uint8_t v___x_4407_; uint8_t v___x_4408_; lean_object* v___x_4409_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc_n(v_a_4402_, 2);
lean_dec_ref_known(v___x_4401_, 1);
v_sz_4403_ = lean_array_size(v_fvarIds_4388_);
v___x_4404_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4388_);
v___x_4405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4403_, v___x_4404_, v_fvarIds_4388_);
v___x_4406_ = 0;
v___x_4407_ = 1;
v___x_4408_ = 1;
v___x_4409_ = l_Lean_Meta_mkLetFVars(v___x_4405_, v_a_4402_, v___x_4406_, v___x_4407_, v___x_4408_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec_ref(v___x_4405_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4421_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4385_, v_a_4410_, v___y_4392_);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4421_ == 0)
{
lean_object* v_unused_4422_; 
v_unused_4422_ = lean_ctor_get(v___x_4411_, 0);
lean_dec(v_unused_4422_);
v___x_4413_ = v___x_4411_;
v_isShared_4414_ = v_isSharedCheck_4421_;
goto v_resetjp_4412_;
}
else
{
lean_dec(v___x_4411_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4421_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4419_; 
v___x_4415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4415_, 0, v_fvarIds_4388_);
lean_ctor_set(v___x_4415_, 1, v_givenNames_x27_4390_);
v___x_4416_ = l_Lean_Expr_mvarId_x21(v_a_4402_);
lean_dec(v_a_4402_);
v___x_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4415_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4417_);
v___x_4419_ = v___x_4413_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_a_4402_);
lean_dec(v_givenNames_x27_4390_);
lean_dec_ref(v_fvarIds_4388_);
lean_dec(v_mvarId_4385_);
v_a_4423_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4409_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4409_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec(v_givenNames_x27_4390_);
lean_dec_ref(v_fvarIds_4388_);
lean_dec(v_mvarId_4385_);
v_a_4431_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4401_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4401_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_givenNames_x27_4390_);
lean_dec_ref(v_fvarIds_4388_);
lean_dec(v_mvarId_4385_);
v_a_4439_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4399_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4399_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
v___jp_4447_:
{
if (v___y_4448_ == 0)
{
lean_dec(v___x_4386_);
goto v___jp_4398_;
}
else
{
lean_object* v___x_4449_; 
lean_inc(v_mvarId_4385_);
v___x_4449_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4386_, v_mvarId_4385_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_dec_ref_known(v___x_4449_, 1);
goto v___jp_4398_;
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec(v_givenNames_x27_4390_);
lean_dec_ref(v_fvarIds_4388_);
lean_dec(v_mvarId_4385_);
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4449_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4449_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4461_, lean_object* v_mvarId_4462_, lean_object* v___x_4463_, lean_object* v_a_4464_, lean_object* v_fvarIds_4465_, lean_object* v_es_4466_, lean_object* v_givenNames_x27_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_MVarId_extractLets___lam__0(v___x_4461_, v_mvarId_4462_, v___x_4463_, v_a_4464_, v_fvarIds_4465_, v_es_4466_, v_givenNames_x27_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec_ref(v_es_4466_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v___x_4461_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4474_, lean_object* v___x_4475_, lean_object* v___x_4476_, lean_object* v_givenNames_4477_, lean_object* v_config_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v___x_4484_; 
lean_inc(v___x_4475_);
lean_inc(v_mvarId_4474_);
v___x_4484_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4474_, v___x_4475_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v___x_4485_; 
lean_dec_ref_known(v___x_4484_, 1);
lean_inc(v_mvarId_4474_);
v___x_4485_ = l_Lean_MVarId_getType(v_mvarId_4474_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___f_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc_n(v_a_4486_, 2);
lean_dec_ref_known(v___x_4485_, 1);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4487_, 0, v___x_4476_);
lean_closure_set(v___f_4487_, 1, v_mvarId_4474_);
lean_closure_set(v___f_4487_, 2, v___x_4475_);
lean_closure_set(v___f_4487_, 3, v_a_4486_);
v___x_4488_ = lean_unsigned_to_nat(1u);
v___x_4489_ = lean_mk_empty_array_with_capacity(v___x_4488_);
v___x_4490_ = lean_array_push(v___x_4489_, v_a_4486_);
v___x_4491_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4490_, v_givenNames_4477_, v___f_4487_, v_config_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_givenNames_4477_);
lean_dec_ref(v___x_4476_);
lean_dec(v___x_4475_);
lean_dec(v_mvarId_4474_);
v_a_4492_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4485_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4485_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec(v_givenNames_4477_);
lean_dec_ref(v___x_4476_);
lean_dec(v___x_4475_);
lean_dec(v_mvarId_4474_);
v_a_4500_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4484_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4484_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4508_, lean_object* v___x_4509_, lean_object* v___x_4510_, lean_object* v_givenNames_4511_, lean_object* v_config_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4508_, v___x_4509_, v___x_4510_, v_givenNames_4511_, v_config_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec_ref(v_config_4512_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4522_, lean_object* v_givenNames_4523_, lean_object* v_config_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___f_4532_; lean_object* v___x_4533_; 
v___x_4530_ = l_Lean_instInhabitedExpr;
v___x_4531_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4522_);
v___f_4532_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4532_, 0, v_mvarId_4522_);
lean_closure_set(v___f_4532_, 1, v___x_4531_);
lean_closure_set(v___f_4532_, 2, v___x_4530_);
lean_closure_set(v___f_4532_, 3, v_givenNames_4523_);
lean_closure_set(v___f_4532_, 4, v_config_4524_);
v___x_4533_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4522_, v___f_4532_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4534_, lean_object* v_givenNames_4535_, lean_object* v_config_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_MVarId_extractLets(v_mvarId_4534_, v_givenNames_4535_, v_config_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4543_, lean_object* v_val_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4543_, v_val_4544_, v___y_4546_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4551_, lean_object* v_val_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4551_, v_val_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4559_, lean_object* v_x_4560_, lean_object* v_x_4561_, lean_object* v_x_4562_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4560_, v_x_4561_, v_x_4562_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4564_, lean_object* v_x_4565_, size_t v_x_4566_, size_t v_x_4567_, lean_object* v_x_4568_, lean_object* v_x_4569_){
_start:
{
lean_object* v___x_4570_; 
v___x_4570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4565_, v_x_4566_, v_x_4567_, v_x_4568_, v_x_4569_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4571_, lean_object* v_x_4572_, lean_object* v_x_4573_, lean_object* v_x_4574_, lean_object* v_x_4575_, lean_object* v_x_4576_){
_start:
{
size_t v_x_2812__boxed_4577_; size_t v_x_2813__boxed_4578_; lean_object* v_res_4579_; 
v_x_2812__boxed_4577_ = lean_unbox_usize(v_x_4573_);
lean_dec(v_x_4573_);
v_x_2813__boxed_4578_ = lean_unbox_usize(v_x_4574_);
lean_dec(v_x_4574_);
v_res_4579_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4571_, v_x_4572_, v_x_2812__boxed_4577_, v_x_2813__boxed_4578_, v_x_4575_, v_x_4576_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4580_, lean_object* v_n_4581_, lean_object* v_k_4582_, lean_object* v_v_4583_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4581_, v_k_4582_, v_v_4583_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4585_, size_t v_depth_4586_, lean_object* v_keys_4587_, lean_object* v_vals_4588_, lean_object* v_heq_4589_, lean_object* v_i_4590_, lean_object* v_entries_4591_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4586_, v_keys_4587_, v_vals_4588_, v_i_4590_, v_entries_4591_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4593_, lean_object* v_depth_4594_, lean_object* v_keys_4595_, lean_object* v_vals_4596_, lean_object* v_heq_4597_, lean_object* v_i_4598_, lean_object* v_entries_4599_){
_start:
{
size_t v_depth_boxed_4600_; lean_object* v_res_4601_; 
v_depth_boxed_4600_ = lean_unbox_usize(v_depth_4594_);
lean_dec(v_depth_4594_);
v_res_4601_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4593_, v_depth_boxed_4600_, v_keys_4595_, v_vals_4596_, v_heq_4597_, v_i_4598_, v_entries_4599_);
lean_dec_ref(v_vals_4596_);
lean_dec_ref(v_keys_4595_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4602_, lean_object* v_x_4603_, lean_object* v_x_4604_, lean_object* v_x_4605_, lean_object* v_x_4606_){
_start:
{
lean_object* v___x_4607_; 
v___x_4607_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4603_, v_x_4604_, v_x_4605_, v_x_4606_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4608_, size_t v_i_4609_, lean_object* v_bs_4610_){
_start:
{
uint8_t v___x_4611_; 
v___x_4611_ = lean_usize_dec_lt(v_i_4609_, v_sz_4608_);
if (v___x_4611_ == 0)
{
return v_bs_4610_;
}
else
{
lean_object* v_v_4612_; lean_object* v___x_4613_; lean_object* v_bs_x27_4614_; lean_object* v___x_4615_; size_t v___x_4616_; size_t v___x_4617_; lean_object* v___x_4618_; 
v_v_4612_ = lean_array_uget(v_bs_4610_, v_i_4609_);
v___x_4613_ = lean_unsigned_to_nat(0u);
v_bs_x27_4614_ = lean_array_uset(v_bs_4610_, v_i_4609_, v___x_4613_);
v___x_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4615_, 0, v_v_4612_);
v___x_4616_ = ((size_t)1ULL);
v___x_4617_ = lean_usize_add(v_i_4609_, v___x_4616_);
v___x_4618_ = lean_array_uset(v_bs_x27_4614_, v_i_4609_, v___x_4615_);
v_i_4609_ = v___x_4617_;
v_bs_4610_ = v___x_4618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4620_, lean_object* v_i_4621_, lean_object* v_bs_4622_){
_start:
{
size_t v_sz_boxed_4623_; size_t v_i_boxed_4624_; lean_object* v_res_4625_; 
v_sz_boxed_4623_ = lean_unbox_usize(v_sz_4620_);
lean_dec(v_sz_4620_);
v_i_boxed_4624_ = lean_unbox_usize(v_i_4621_);
lean_dec(v_i_4621_);
v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4623_, v_i_boxed_4624_, v_bs_4622_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4626_, lean_object* v_fvars_4627_, lean_object* v_fvarIds_4628_, lean_object* v_givenNames_x27_4629_, lean_object* v_targetNew_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v___x_4636_; 
lean_inc(v_mvarId_4626_);
v___x_4636_ = l_Lean_MVarId_getTag(v_mvarId_4626_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4638_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4636_, 1);
v___x_4638_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4630_, v_a_4637_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; size_t v_sz_4640_; size_t v___x_4641_; lean_object* v___x_4642_; uint8_t v___x_4643_; uint8_t v___x_4644_; uint8_t v___x_4645_; lean_object* v___x_4646_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
lean_inc_n(v_a_4639_, 2);
lean_dec_ref_known(v___x_4638_, 1);
v_sz_4640_ = lean_array_size(v_fvarIds_4628_);
v___x_4641_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4628_);
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4640_, v___x_4641_, v_fvarIds_4628_);
v___x_4643_ = 0;
v___x_4644_ = 1;
v___x_4645_ = 1;
v___x_4646_ = l_Lean_Meta_mkLetFVars(v___x_4642_, v_a_4639_, v___x_4643_, v___x_4644_, v___x_4645_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec_ref(v___x_4642_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4661_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v___x_4646_, 1);
v___x_4648_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4626_, v_a_4647_, v___y_4632_);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; 
v_unused_4662_ = lean_ctor_get(v___x_4648_, 0);
lean_dec(v_unused_4662_);
v___x_4650_ = v___x_4648_;
v_isShared_4651_ = v_isSharedCheck_4661_;
goto v_resetjp_4649_;
}
else
{
lean_dec(v___x_4648_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4661_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4652_; size_t v_sz_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4652_, 0, v_fvarIds_4628_);
lean_ctor_set(v___x_4652_, 1, v_givenNames_x27_4629_);
v_sz_4653_ = lean_array_size(v_fvars_4627_);
v___x_4654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4653_, v___x_4641_, v_fvars_4627_);
v___x_4655_ = l_Lean_Expr_mvarId_x21(v_a_4639_);
lean_dec(v_a_4639_);
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4654_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4652_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 0, v___x_4657_);
v___x_4659_ = v___x_4650_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec(v_a_4639_);
lean_dec(v_givenNames_x27_4629_);
lean_dec_ref(v_fvarIds_4628_);
lean_dec_ref(v_fvars_4627_);
lean_dec(v_mvarId_4626_);
v_a_4663_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4646_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4646_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec(v_givenNames_x27_4629_);
lean_dec_ref(v_fvarIds_4628_);
lean_dec_ref(v_fvars_4627_);
lean_dec(v_mvarId_4626_);
v_a_4671_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4638_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4638_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_dec_ref(v_targetNew_4630_);
lean_dec(v_givenNames_x27_4629_);
lean_dec_ref(v_fvarIds_4628_);
lean_dec_ref(v_fvars_4627_);
lean_dec(v_mvarId_4626_);
v_a_4679_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4636_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4636_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4687_, lean_object* v_fvars_4688_, lean_object* v_fvarIds_4689_, lean_object* v_givenNames_x27_4690_, lean_object* v_targetNew_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4687_, v_fvars_4688_, v_fvarIds_4689_, v_givenNames_x27_4690_, v_targetNew_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4698_, lean_object* v_binderName_4699_, lean_object* v_body_4700_, uint8_t v_binderInfo_4701_, lean_object* v___f_4702_, lean_object* v___x_4703_, lean_object* v_mvarId_4704_, lean_object* v_binderType_4705_, lean_object* v_fvarIds_4706_, lean_object* v_es_4707_, lean_object* v_givenNames_x27_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; uint8_t v___y_4720_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
v___x_4714_ = lean_unsigned_to_nat(0u);
v___x_4715_ = lean_array_get_borrowed(v___x_4698_, v_es_4707_, v___x_4714_);
v___x_4730_ = lean_array_get_size(v_fvarIds_4706_);
v___x_4731_ = lean_nat_dec_eq(v___x_4730_, v___x_4714_);
if (v___x_4731_ == 0)
{
v___y_4720_ = v___x_4731_;
goto v___jp_4719_;
}
else
{
uint8_t v___x_4732_; 
v___x_4732_ = lean_expr_eqv(v_binderType_4705_, v___x_4715_);
v___y_4720_ = v___x_4732_;
goto v___jp_4719_;
}
v___jp_4716_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; 
lean_inc(v___x_4715_);
v___x_4717_ = l_Lean_Expr_forallE___override(v_binderName_4699_, v___x_4715_, v_body_4700_, v_binderInfo_4701_);
lean_inc(v___y_4712_);
lean_inc_ref(v___y_4711_);
lean_inc(v___y_4710_);
lean_inc_ref(v___y_4709_);
v___x_4718_ = lean_apply_8(v___f_4702_, v_fvarIds_4706_, v_givenNames_x27_4708_, v___x_4717_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, lean_box(0));
return v___x_4718_;
}
v___jp_4719_:
{
if (v___y_4720_ == 0)
{
lean_dec(v_mvarId_4704_);
lean_dec(v___x_4703_);
goto v___jp_4716_;
}
else
{
lean_object* v___x_4721_; 
v___x_4721_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4703_, v_mvarId_4704_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_dec_ref_known(v___x_4721_, 1);
goto v___jp_4716_;
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_dec(v_givenNames_x27_4708_);
lean_dec_ref(v_fvarIds_4706_);
lean_dec_ref(v___f_4702_);
lean_dec_ref(v_body_4700_);
lean_dec(v_binderName_4699_);
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4733_, lean_object* v_binderName_4734_, lean_object* v_body_4735_, lean_object* v_binderInfo_4736_, lean_object* v___f_4737_, lean_object* v___x_4738_, lean_object* v_mvarId_4739_, lean_object* v_binderType_4740_, lean_object* v_fvarIds_4741_, lean_object* v_es_4742_, lean_object* v_givenNames_x27_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
uint8_t v_binderInfo_1854__boxed_4749_; lean_object* v_res_4750_; 
v_binderInfo_1854__boxed_4749_ = lean_unbox(v_binderInfo_4736_);
v_res_4750_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4733_, v_binderName_4734_, v_body_4735_, v_binderInfo_1854__boxed_4749_, v___f_4737_, v___x_4738_, v_mvarId_4739_, v_binderType_4740_, v_fvarIds_4741_, v_es_4742_, v_givenNames_x27_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec_ref(v_es_4742_);
lean_dec_ref(v_binderType_4740_);
lean_dec_ref(v___x_4733_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4751_, lean_object* v_declName_4752_, lean_object* v_body_4753_, uint8_t v_nondep_4754_, lean_object* v___f_4755_, lean_object* v_value_4756_, lean_object* v___x_4757_, lean_object* v_mvarId_4758_, lean_object* v_type_4759_, lean_object* v_fvarIds_4760_, lean_object* v_es_4761_, lean_object* v_givenNames_x27_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; uint8_t v___y_4776_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4768_ = lean_unsigned_to_nat(0u);
v___x_4769_ = lean_array_get_borrowed(v___x_4751_, v_es_4761_, v___x_4768_);
v___x_4770_ = lean_unsigned_to_nat(1u);
v___x_4771_ = lean_array_get_borrowed(v___x_4751_, v_es_4761_, v___x_4770_);
v___x_4787_ = lean_array_get_size(v_fvarIds_4760_);
v___x_4788_ = lean_nat_dec_eq(v___x_4787_, v___x_4768_);
if (v___x_4788_ == 0)
{
v___y_4776_ = v___x_4788_;
goto v___jp_4775_;
}
else
{
uint8_t v___x_4789_; 
v___x_4789_ = lean_expr_eqv(v_type_4759_, v___x_4769_);
v___y_4776_ = v___x_4789_;
goto v___jp_4775_;
}
v___jp_4772_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
lean_inc(v___x_4771_);
lean_inc(v___x_4769_);
v___x_4773_ = l_Lean_Expr_letE___override(v_declName_4752_, v___x_4769_, v___x_4771_, v_body_4753_, v_nondep_4754_);
lean_inc(v___y_4766_);
lean_inc_ref(v___y_4765_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
v___x_4774_ = lean_apply_8(v___f_4755_, v_fvarIds_4760_, v_givenNames_x27_4762_, v___x_4773_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, lean_box(0));
return v___x_4774_;
}
v___jp_4775_:
{
if (v___y_4776_ == 0)
{
lean_dec(v_mvarId_4758_);
lean_dec(v___x_4757_);
goto v___jp_4772_;
}
else
{
uint8_t v___x_4777_; 
v___x_4777_ = lean_expr_eqv(v_value_4756_, v___x_4771_);
if (v___x_4777_ == 0)
{
lean_dec(v_mvarId_4758_);
lean_dec(v___x_4757_);
goto v___jp_4772_;
}
else
{
lean_object* v___x_4778_; 
v___x_4778_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4757_, v_mvarId_4758_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_dec_ref_known(v___x_4778_, 1);
goto v___jp_4772_;
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
lean_dec(v_givenNames_x27_4762_);
lean_dec_ref(v_fvarIds_4760_);
lean_dec_ref(v___f_4755_);
lean_dec_ref(v_body_4753_);
lean_dec(v_declName_4752_);
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4778_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4778_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4790_ = _args[0];
lean_object* v_declName_4791_ = _args[1];
lean_object* v_body_4792_ = _args[2];
lean_object* v_nondep_4793_ = _args[3];
lean_object* v___f_4794_ = _args[4];
lean_object* v_value_4795_ = _args[5];
lean_object* v___x_4796_ = _args[6];
lean_object* v_mvarId_4797_ = _args[7];
lean_object* v_type_4798_ = _args[8];
lean_object* v_fvarIds_4799_ = _args[9];
lean_object* v_es_4800_ = _args[10];
lean_object* v_givenNames_x27_4801_ = _args[11];
lean_object* v___y_4802_ = _args[12];
lean_object* v___y_4803_ = _args[13];
lean_object* v___y_4804_ = _args[14];
lean_object* v___y_4805_ = _args[15];
lean_object* v___y_4806_ = _args[16];
_start:
{
uint8_t v_nondep_1929__boxed_4807_; lean_object* v_res_4808_; 
v_nondep_1929__boxed_4807_ = lean_unbox(v_nondep_4793_);
v_res_4808_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4790_, v_declName_4791_, v_body_4792_, v_nondep_1929__boxed_4807_, v___f_4794_, v_value_4795_, v___x_4796_, v_mvarId_4797_, v_type_4798_, v_fvarIds_4799_, v_es_4800_, v_givenNames_x27_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec_ref(v_es_4800_);
lean_dec_ref(v_type_4798_);
lean_dec_ref(v_value_4795_);
lean_dec_ref(v___x_4790_);
return v_res_4808_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4813_ = l_Lean_MessageData_ofFormat(v___x_4812_);
return v___x_4813_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4816_, lean_object* v___x_4817_, lean_object* v___f_4818_, lean_object* v___x_4819_, lean_object* v_givenNames_4820_, lean_object* v_config_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_){
_start:
{
lean_object* v___x_4827_; 
lean_inc(v_mvarId_4816_);
v___x_4827_ = l_Lean_MVarId_getType(v_mvarId_4816_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v___x_4827_, 1);
switch(lean_obj_tag(v_a_4828_))
{
case 7:
{
lean_object* v_binderName_4829_; lean_object* v_binderType_4830_; lean_object* v_body_4831_; uint8_t v_binderInfo_4832_; lean_object* v___x_4833_; lean_object* v___f_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v_binderName_4829_ = lean_ctor_get(v_a_4828_, 0);
lean_inc(v_binderName_4829_);
v_binderType_4830_ = lean_ctor_get(v_a_4828_, 1);
lean_inc_ref_n(v_binderType_4830_, 2);
v_body_4831_ = lean_ctor_get(v_a_4828_, 2);
lean_inc_ref(v_body_4831_);
v_binderInfo_4832_ = lean_ctor_get_uint8(v_a_4828_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4828_, 3);
v___x_4833_ = lean_box(v_binderInfo_4832_);
v___f_4834_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4834_, 0, v___x_4817_);
lean_closure_set(v___f_4834_, 1, v_binderName_4829_);
lean_closure_set(v___f_4834_, 2, v_body_4831_);
lean_closure_set(v___f_4834_, 3, v___x_4833_);
lean_closure_set(v___f_4834_, 4, v___f_4818_);
lean_closure_set(v___f_4834_, 5, v___x_4819_);
lean_closure_set(v___f_4834_, 6, v_mvarId_4816_);
lean_closure_set(v___f_4834_, 7, v_binderType_4830_);
v___x_4835_ = lean_unsigned_to_nat(1u);
v___x_4836_ = lean_mk_empty_array_with_capacity(v___x_4835_);
v___x_4837_ = lean_array_push(v___x_4836_, v_binderType_4830_);
v___x_4838_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4837_, v_givenNames_4820_, v___f_4834_, v_config_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_);
return v___x_4838_;
}
case 8:
{
lean_object* v_declName_4839_; lean_object* v_type_4840_; lean_object* v_value_4841_; lean_object* v_body_4842_; uint8_t v_nondep_4843_; lean_object* v___x_4844_; lean_object* v___f_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v_declName_4839_ = lean_ctor_get(v_a_4828_, 0);
lean_inc(v_declName_4839_);
v_type_4840_ = lean_ctor_get(v_a_4828_, 1);
lean_inc_ref_n(v_type_4840_, 2);
v_value_4841_ = lean_ctor_get(v_a_4828_, 2);
lean_inc_ref_n(v_value_4841_, 2);
v_body_4842_ = lean_ctor_get(v_a_4828_, 3);
lean_inc_ref(v_body_4842_);
v_nondep_4843_ = lean_ctor_get_uint8(v_a_4828_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_4828_, 4);
v___x_4844_ = lean_box(v_nondep_4843_);
v___f_4845_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4845_, 0, v___x_4817_);
lean_closure_set(v___f_4845_, 1, v_declName_4839_);
lean_closure_set(v___f_4845_, 2, v_body_4842_);
lean_closure_set(v___f_4845_, 3, v___x_4844_);
lean_closure_set(v___f_4845_, 4, v___f_4818_);
lean_closure_set(v___f_4845_, 5, v_value_4841_);
lean_closure_set(v___f_4845_, 6, v___x_4819_);
lean_closure_set(v___f_4845_, 7, v_mvarId_4816_);
lean_closure_set(v___f_4845_, 8, v_type_4840_);
v___x_4846_ = lean_unsigned_to_nat(2u);
v___x_4847_ = lean_mk_empty_array_with_capacity(v___x_4846_);
v___x_4848_ = lean_array_push(v___x_4847_, v_type_4840_);
v___x_4849_ = lean_array_push(v___x_4848_, v_value_4841_);
v___x_4850_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4849_, v_givenNames_4820_, v___f_4845_, v_config_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_);
return v___x_4850_;
}
default: 
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
lean_dec(v_a_4828_);
lean_dec(v_givenNames_4820_);
lean_dec_ref(v___f_4818_);
lean_dec_ref(v___x_4817_);
v___x_4851_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4852_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4819_, v_mvarId_4816_, v___x_4851_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_);
return v___x_4852_;
}
}
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec(v_givenNames_4820_);
lean_dec(v___x_4819_);
lean_dec_ref(v___f_4818_);
lean_dec_ref(v___x_4817_);
lean_dec(v_mvarId_4816_);
v_a_4853_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4827_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4827_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4861_, lean_object* v___x_4862_, lean_object* v___f_4863_, lean_object* v___x_4864_, lean_object* v_givenNames_4865_, lean_object* v_config_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4861_, v___x_4862_, v___f_4863_, v___x_4864_, v_givenNames_4865_, v_config_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec_ref(v_config_4866_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4873_, lean_object* v___x_4874_, lean_object* v_givenNames_4875_, lean_object* v_config_4876_, lean_object* v_mvarId_4877_, lean_object* v_fvars_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v___f_4884_; lean_object* v___f_4885_; lean_object* v___x_4886_; 
lean_inc_n(v_mvarId_4877_, 2);
v___f_4884_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4884_, 0, v_mvarId_4877_);
lean_closure_set(v___f_4884_, 1, v_fvars_4878_);
v___f_4885_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4885_, 0, v_mvarId_4877_);
lean_closure_set(v___f_4885_, 1, v___x_4873_);
lean_closure_set(v___f_4885_, 2, v___f_4884_);
lean_closure_set(v___f_4885_, 3, v___x_4874_);
lean_closure_set(v___f_4885_, 4, v_givenNames_4875_);
lean_closure_set(v___f_4885_, 5, v_config_4876_);
v___x_4886_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4877_, v___f_4885_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4887_, lean_object* v___x_4888_, lean_object* v_givenNames_4889_, lean_object* v_config_4890_, lean_object* v_mvarId_4891_, lean_object* v_fvars_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4887_, v___x_4888_, v_givenNames_4889_, v_config_4890_, v_mvarId_4891_, v_fvars_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4899_, lean_object* v_fvarId_4900_, lean_object* v_givenNames_4901_, lean_object* v_config_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4899_);
v___x_4909_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4899_, v___x_4908_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4910_; lean_object* v___f_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; lean_object* v___x_4916_; 
lean_dec_ref_known(v___x_4909_, 1);
v___x_4910_ = l_Lean_instInhabitedExpr;
v___f_4911_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4911_, 0, v___x_4910_);
lean_closure_set(v___f_4911_, 1, v___x_4908_);
lean_closure_set(v___f_4911_, 2, v_givenNames_4901_);
lean_closure_set(v___f_4911_, 3, v_config_4902_);
v___x_4912_ = lean_unsigned_to_nat(1u);
v___x_4913_ = lean_mk_empty_array_with_capacity(v___x_4912_);
v___x_4914_ = lean_array_push(v___x_4913_, v_fvarId_4900_);
v___x_4915_ = 0;
v___x_4916_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4899_, v___x_4914_, v___f_4911_, v___x_4915_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
return v___x_4916_;
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec_ref(v_config_4902_);
lean_dec(v_givenNames_4901_);
lean_dec(v_fvarId_4900_);
lean_dec(v_mvarId_4899_);
v_a_4917_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4909_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4909_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4925_, lean_object* v_fvarId_4926_, lean_object* v_givenNames_4927_, lean_object* v_config_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4925_, v_fvarId_4926_, v_givenNames_4927_, v_config_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4935_, lean_object* v___x_4936_, lean_object* v_config_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v___x_4943_; 
lean_inc(v___x_4936_);
lean_inc(v_mvarId_4935_);
v___x_4943_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4935_, v___x_4936_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v___x_4944_; 
lean_dec_ref_known(v___x_4943_, 1);
lean_inc(v_mvarId_4935_);
v___x_4944_ = l_Lean_MVarId_getType(v_mvarId_4935_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4946_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc_n(v_a_4945_, 2);
lean_dec_ref_known(v___x_4944_, 1);
v___x_4946_ = l_Lean_Meta_liftLets(v_a_4945_, v_config_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; uint8_t v___x_4948_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4948_ = lean_expr_eqv(v_a_4945_, v_a_4947_);
lean_dec(v_a_4945_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; 
lean_dec(v___x_4936_);
v___x_4949_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4935_, v_a_4947_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
return v___x_4949_;
}
else
{
lean_object* v___x_4950_; 
lean_inc(v_mvarId_4935_);
v___x_4950_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4936_, v_mvarId_4935_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v___x_4951_; 
lean_dec_ref_known(v___x_4950_, 1);
v___x_4951_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4935_, v_a_4947_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
return v___x_4951_;
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec(v_a_4947_);
lean_dec(v_mvarId_4935_);
v_a_4952_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4950_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4950_);
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
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
lean_dec(v_a_4945_);
lean_dec(v___x_4936_);
lean_dec(v_mvarId_4935_);
v_a_4960_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4946_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4946_);
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
else
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_dec_ref(v_config_4937_);
lean_dec(v___x_4936_);
lean_dec(v_mvarId_4935_);
v_a_4968_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4944_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4944_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec_ref(v_config_4937_);
lean_dec(v___x_4936_);
lean_dec(v_mvarId_4935_);
v_a_4976_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4943_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4943_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4984_, lean_object* v___x_4985_, lean_object* v_config_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4984_, v___x_4985_, v_config_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4996_, lean_object* v_config_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v___x_5003_; lean_object* v___f_5004_; lean_object* v___x_5005_; 
v___x_5003_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4996_);
v___f_5004_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5004_, 0, v_mvarId_4996_);
lean_closure_set(v___f_5004_, 1, v___x_5003_);
lean_closure_set(v___f_5004_, 2, v_config_4997_);
v___x_5005_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4996_, v___f_5004_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_5006_, lean_object* v_config_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_MVarId_liftLets(v_mvarId_5006_, v_config_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_5014_, lean_object* v_fvars_5015_, lean_object* v_targetNew_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_5014_, v_targetNew_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5036_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5025_ = v___x_5022_;
v_isShared_5026_ = v_isSharedCheck_5036_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5022_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5036_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5027_; size_t v_sz_5028_; size_t v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5034_; 
v___x_5027_ = lean_box(0);
v_sz_5028_ = lean_array_size(v_fvars_5015_);
v___x_5029_ = ((size_t)0ULL);
v___x_5030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_5028_, v___x_5029_, v_fvars_5015_);
v___x_5031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
lean_ctor_set(v___x_5031_, 1, v_a_5023_);
v___x_5032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5027_);
lean_ctor_set(v___x_5032_, 1, v___x_5031_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 0, v___x_5032_);
v___x_5034_ = v___x_5025_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
else
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5044_; 
lean_dec_ref(v_fvars_5015_);
v_a_5037_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5039_ = v___x_5022_;
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5022_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_5045_, lean_object* v_fvars_5046_, lean_object* v_targetNew_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_5045_, v_fvars_5046_, v_targetNew_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_5054_, lean_object* v_config_5055_, lean_object* v___f_5056_, lean_object* v___x_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
lean_object* v___x_5063_; 
lean_inc(v_mvarId_5054_);
v___x_5063_ = l_Lean_MVarId_getType(v_mvarId_5054_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5063_, 1);
switch(lean_obj_tag(v_a_5064_))
{
case 7:
{
lean_object* v_binderName_5065_; lean_object* v_binderType_5066_; lean_object* v_body_5067_; uint8_t v_binderInfo_5068_; lean_object* v___x_5069_; 
v_binderName_5065_ = lean_ctor_get(v_a_5064_, 0);
lean_inc(v_binderName_5065_);
v_binderType_5066_ = lean_ctor_get(v_a_5064_, 1);
lean_inc_ref_n(v_binderType_5066_, 2);
v_body_5067_ = lean_ctor_get(v_a_5064_, 2);
lean_inc_ref(v_body_5067_);
v_binderInfo_5068_ = lean_ctor_get_uint8(v_a_5064_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_5064_, 3);
v___x_5069_ = l_Lean_Meta_liftLets(v_binderType_5066_, v_config_5055_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5069_) == 0)
{
lean_object* v_a_5070_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; uint8_t v___x_5078_; 
v_a_5070_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_a_5070_);
lean_dec_ref_known(v___x_5069_, 1);
v___x_5078_ = lean_expr_eqv(v_binderType_5066_, v_a_5070_);
lean_dec_ref(v_binderType_5066_);
if (v___x_5078_ == 0)
{
lean_dec(v___x_5057_);
lean_dec(v_mvarId_5054_);
v___y_5072_ = v___y_5058_;
v___y_5073_ = v___y_5059_;
v___y_5074_ = v___y_5060_;
v___y_5075_ = v___y_5061_;
goto v___jp_5071_;
}
else
{
lean_object* v___x_5079_; 
v___x_5079_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_5057_, v_mvarId_5054_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_dec_ref_known(v___x_5079_, 1);
v___y_5072_ = v___y_5058_;
v___y_5073_ = v___y_5059_;
v___y_5074_ = v___y_5060_;
v___y_5075_ = v___y_5061_;
goto v___jp_5071_;
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
lean_dec(v_a_5070_);
lean_dec_ref(v_body_5067_);
lean_dec(v_binderName_5065_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec_ref(v___f_5056_);
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_5079_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5079_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
v___jp_5071_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = l_Lean_Expr_forallE___override(v_binderName_5065_, v_a_5070_, v_body_5067_, v_binderInfo_5068_);
v___x_5077_ = lean_apply_6(v___f_5056_, v___x_5076_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, lean_box(0));
return v___x_5077_;
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_dec_ref(v_body_5067_);
lean_dec_ref(v_binderType_5066_);
lean_dec(v_binderName_5065_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v___f_5056_);
lean_dec(v_mvarId_5054_);
v_a_5088_ = lean_ctor_get(v___x_5069_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5069_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5069_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
case 8:
{
lean_object* v_declName_5096_; lean_object* v_type_5097_; lean_object* v_value_5098_; lean_object* v_body_5099_; uint8_t v_nondep_5100_; lean_object* v___x_5101_; 
v_declName_5096_ = lean_ctor_get(v_a_5064_, 0);
lean_inc(v_declName_5096_);
v_type_5097_ = lean_ctor_get(v_a_5064_, 1);
lean_inc_ref_n(v_type_5097_, 2);
v_value_5098_ = lean_ctor_get(v_a_5064_, 2);
lean_inc_ref(v_value_5098_);
v_body_5099_ = lean_ctor_get(v_a_5064_, 3);
lean_inc_ref(v_body_5099_);
v_nondep_5100_ = lean_ctor_get_uint8(v_a_5064_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_5064_, 4);
lean_inc_ref(v_config_5055_);
v___x_5101_ = l_Lean_Meta_liftLets(v_type_5097_, v_config_5055_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v___x_5103_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5101_, 1);
lean_inc_ref(v_value_5098_);
v___x_5103_ = l_Lean_Meta_liftLets(v_value_5098_, v_config_5055_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_a_5104_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; uint8_t v___y_5113_; uint8_t v___x_5123_; 
v_a_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5103_, 1);
v___x_5123_ = lean_expr_eqv(v_type_5097_, v_a_5102_);
lean_dec_ref(v_type_5097_);
if (v___x_5123_ == 0)
{
lean_dec_ref(v_value_5098_);
v___y_5113_ = v___x_5123_;
goto v___jp_5112_;
}
else
{
uint8_t v___x_5124_; 
v___x_5124_ = lean_expr_eqv(v_value_5098_, v_a_5104_);
lean_dec_ref(v_value_5098_);
v___y_5113_ = v___x_5124_;
goto v___jp_5112_;
}
v___jp_5105_:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5110_ = l_Lean_Expr_letE___override(v_declName_5096_, v_a_5102_, v_a_5104_, v_body_5099_, v_nondep_5100_);
v___x_5111_ = lean_apply_6(v___f_5056_, v___x_5110_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, lean_box(0));
return v___x_5111_;
}
v___jp_5112_:
{
if (v___y_5113_ == 0)
{
lean_dec(v___x_5057_);
lean_dec(v_mvarId_5054_);
v___y_5106_ = v___y_5058_;
v___y_5107_ = v___y_5059_;
v___y_5108_ = v___y_5060_;
v___y_5109_ = v___y_5061_;
goto v___jp_5105_;
}
else
{
lean_object* v___x_5114_; 
v___x_5114_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_5057_, v_mvarId_5054_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_dec_ref_known(v___x_5114_, 1);
v___y_5106_ = v___y_5058_;
v___y_5107_ = v___y_5059_;
v___y_5108_ = v___y_5060_;
v___y_5109_ = v___y_5061_;
goto v___jp_5105_;
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
lean_dec(v_a_5104_);
lean_dec(v_a_5102_);
lean_dec_ref(v_body_5099_);
lean_dec(v_declName_5096_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec_ref(v___f_5056_);
v_a_5115_ = lean_ctor_get(v___x_5114_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5114_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5114_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_dec(v_a_5102_);
lean_dec_ref(v_body_5099_);
lean_dec_ref(v_value_5098_);
lean_dec_ref(v_type_5097_);
lean_dec(v_declName_5096_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v___f_5056_);
lean_dec(v_mvarId_5054_);
v_a_5125_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5103_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5103_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
else
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
lean_dec_ref(v_body_5099_);
lean_dec_ref(v_value_5098_);
lean_dec_ref(v_type_5097_);
lean_dec(v_declName_5096_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v___f_5056_);
lean_dec_ref(v_config_5055_);
lean_dec(v_mvarId_5054_);
v_a_5133_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_5101_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5101_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
}
default: 
{
lean_object* v___x_5141_; lean_object* v___x_5142_; 
lean_dec(v_a_5064_);
lean_dec_ref(v___f_5056_);
lean_dec_ref(v_config_5055_);
v___x_5141_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_5142_ = l_Lean_Meta_throwTacticEx___redArg(v___x_5057_, v_mvarId_5054_, v___x_5141_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
return v___x_5142_;
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v___f_5056_);
lean_dec_ref(v_config_5055_);
lean_dec(v_mvarId_5054_);
v_a_5143_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5063_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5063_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_5151_, lean_object* v_config_5152_, lean_object* v___f_5153_, lean_object* v___x_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_5151_, v_config_5152_, v___f_5153_, v___x_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_5161_, lean_object* v___x_5162_, lean_object* v_mvarId_5163_, lean_object* v_fvars_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_){
_start:
{
lean_object* v___f_5170_; lean_object* v___f_5171_; lean_object* v___x_5172_; 
lean_inc_n(v_mvarId_5163_, 2);
v___f_5170_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5170_, 0, v_mvarId_5163_);
lean_closure_set(v___f_5170_, 1, v_fvars_5164_);
v___f_5171_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_5171_, 0, v_mvarId_5163_);
lean_closure_set(v___f_5171_, 1, v_config_5161_);
lean_closure_set(v___f_5171_, 2, v___f_5170_);
lean_closure_set(v___f_5171_, 3, v___x_5162_);
v___x_5172_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5163_, v___f_5171_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_);
return v___x_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_5173_, lean_object* v___x_5174_, lean_object* v_mvarId_5175_, lean_object* v_fvars_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_5173_, v___x_5174_, v_mvarId_5175_, v_fvars_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_5183_, lean_object* v_fvarId_5184_, lean_object* v_config_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_){
_start:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5191_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_5183_);
v___x_5192_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_5183_, v___x_5191_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
if (lean_obj_tag(v___x_5192_) == 0)
{
lean_object* v___f_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; lean_object* v___x_5198_; 
lean_dec_ref_known(v___x_5192_, 1);
v___f_5193_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_5193_, 0, v_config_5185_);
lean_closure_set(v___f_5193_, 1, v___x_5191_);
v___x_5194_ = lean_unsigned_to_nat(1u);
v___x_5195_ = lean_mk_empty_array_with_capacity(v___x_5194_);
v___x_5196_ = lean_array_push(v___x_5195_, v_fvarId_5184_);
v___x_5197_ = 0;
v___x_5198_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_5183_, v___x_5196_, v___f_5193_, v___x_5197_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5207_; 
v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5198_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5201_ = v___x_5198_;
v_isShared_5202_ = v_isSharedCheck_5207_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5198_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5207_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v_snd_5203_; lean_object* v___x_5205_; 
v_snd_5203_ = lean_ctor_get(v_a_5199_, 1);
lean_inc(v_snd_5203_);
lean_dec(v_a_5199_);
if (v_isShared_5202_ == 0)
{
lean_ctor_set(v___x_5201_, 0, v_snd_5203_);
v___x_5205_ = v___x_5201_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_snd_5203_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
v_a_5208_ = lean_ctor_get(v___x_5198_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5198_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5198_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5198_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
lean_dec_ref(v_config_5185_);
lean_dec(v_fvarId_5184_);
lean_dec(v_mvarId_5183_);
v_a_5216_ = lean_ctor_get(v___x_5192_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5192_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5192_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5192_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_5224_, lean_object* v_fvarId_5225_, lean_object* v_config_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_){
_start:
{
lean_object* v_res_5232_; 
v_res_5232_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_5224_, v_fvarId_5225_, v_config_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
lean_dec(v_a_5230_);
lean_dec_ref(v_a_5229_);
lean_dec(v_a_5228_);
lean_dec_ref(v_a_5227_);
return v_res_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_5233_, lean_object* v___x_5234_, uint8_t v_failIfUnchanged_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
lean_object* v___x_5241_; 
lean_inc(v___x_5234_);
lean_inc(v_mvarId_5233_);
v___x_5241_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_5233_, v___x_5234_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
if (lean_obj_tag(v___x_5241_) == 0)
{
lean_object* v___x_5242_; 
lean_dec_ref_known(v___x_5241_, 1);
lean_inc(v_mvarId_5233_);
v___x_5242_ = l_Lean_MVarId_getType(v_mvarId_5233_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5244_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc_n(v_a_5243_, 2);
lean_dec_ref_known(v___x_5242_, 1);
v___x_5244_ = l_Lean_Meta_letToHave(v_a_5243_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
if (lean_obj_tag(v___x_5244_) == 0)
{
if (v_failIfUnchanged_5235_ == 0)
{
lean_object* v_a_5245_; lean_object* v___x_5246_; 
lean_dec(v_a_5243_);
lean_dec(v___x_5234_);
v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
lean_inc(v_a_5245_);
lean_dec_ref_known(v___x_5244_, 1);
v___x_5246_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_5233_, v_a_5245_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
return v___x_5246_;
}
else
{
lean_object* v_a_5247_; uint8_t v___x_5248_; 
v_a_5247_ = lean_ctor_get(v___x_5244_, 0);
lean_inc(v_a_5247_);
lean_dec_ref_known(v___x_5244_, 1);
v___x_5248_ = lean_expr_eqv(v_a_5243_, v_a_5247_);
lean_dec(v_a_5243_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5249_; 
lean_dec(v___x_5234_);
v___x_5249_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_5233_, v_a_5247_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
return v___x_5249_;
}
else
{
lean_object* v___x_5250_; 
lean_inc(v_mvarId_5233_);
v___x_5250_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_5234_, v_mvarId_5233_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v___x_5251_; 
lean_dec_ref_known(v___x_5250_, 1);
v___x_5251_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_5233_, v_a_5247_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
return v___x_5251_;
}
else
{
lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5259_; 
lean_dec(v_a_5247_);
lean_dec(v_mvarId_5233_);
v_a_5252_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5254_ = v___x_5250_;
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v___x_5250_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5257_; 
if (v_isShared_5255_ == 0)
{
v___x_5257_ = v___x_5254_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_a_5252_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
}
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
lean_dec(v_a_5243_);
lean_dec(v___x_5234_);
lean_dec(v_mvarId_5233_);
v_a_5260_ = lean_ctor_get(v___x_5244_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5244_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5244_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5244_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
else
{
lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5275_; 
lean_dec(v___x_5234_);
lean_dec(v_mvarId_5233_);
v_a_5268_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5270_ = v___x_5242_;
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_dec(v___x_5242_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5273_; 
if (v_isShared_5271_ == 0)
{
v___x_5273_ = v___x_5270_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
v___x_5273_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
return v___x_5273_;
}
}
}
}
else
{
lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5283_; 
lean_dec(v___x_5234_);
lean_dec(v_mvarId_5233_);
v_a_5276_ = lean_ctor_get(v___x_5241_, 0);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5278_ = v___x_5241_;
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_dec(v___x_5241_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5281_; 
if (v_isShared_5279_ == 0)
{
v___x_5281_ = v___x_5278_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
v___x_5281_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
return v___x_5281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_5284_, lean_object* v___x_5285_, lean_object* v_failIfUnchanged_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5292_; lean_object* v_res_5293_; 
v_failIfUnchanged_boxed_5292_ = lean_unbox(v_failIfUnchanged_5286_);
v_res_5293_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_5284_, v___x_5285_, v_failIfUnchanged_boxed_5292_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_5297_, uint8_t v_failIfUnchanged_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___f_5306_; lean_object* v___x_5307_; 
v___x_5304_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5305_ = lean_box(v_failIfUnchanged_5298_);
lean_inc(v_mvarId_5297_);
v___f_5306_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5306_, 0, v_mvarId_5297_);
lean_closure_set(v___f_5306_, 1, v___x_5304_);
lean_closure_set(v___f_5306_, 2, v___x_5305_);
v___x_5307_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5297_, v___f_5306_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_5308_, lean_object* v_failIfUnchanged_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5315_; lean_object* v_res_5316_; 
v_failIfUnchanged_boxed_5315_ = lean_unbox(v_failIfUnchanged_5309_);
v_res_5316_ = l_Lean_MVarId_letToHave(v_mvarId_5308_, v_failIfUnchanged_boxed_5315_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_);
lean_dec(v_a_5313_);
lean_dec_ref(v_a_5312_);
lean_dec(v_a_5311_);
lean_dec_ref(v_a_5310_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_5317_, lean_object* v___x_5318_, lean_object* v_fvarId_5319_, uint8_t v_failIfUnchanged_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v___x_5326_; 
lean_inc(v___x_5318_);
lean_inc(v_mvarId_5317_);
v___x_5326_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_5317_, v___x_5318_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v___x_5327_; 
lean_dec_ref_known(v___x_5326_, 1);
lean_inc(v_fvarId_5319_);
v___x_5327_ = l_Lean_FVarId_getType___redArg(v_fvarId_5319_, v___y_5321_, v___y_5323_, v___y_5324_);
if (lean_obj_tag(v___x_5327_) == 0)
{
lean_object* v_a_5328_; lean_object* v___x_5329_; 
v_a_5328_ = lean_ctor_get(v___x_5327_, 0);
lean_inc_n(v_a_5328_, 2);
lean_dec_ref_known(v___x_5327_, 1);
v___x_5329_ = l_Lean_Meta_letToHave(v_a_5328_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
if (lean_obj_tag(v___x_5329_) == 0)
{
if (v_failIfUnchanged_5320_ == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5331_; 
lean_dec(v_a_5328_);
lean_dec(v___x_5318_);
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5330_);
lean_dec_ref_known(v___x_5329_, 1);
v___x_5331_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5317_, v_fvarId_5319_, v_a_5330_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
return v___x_5331_;
}
else
{
lean_object* v_a_5332_; uint8_t v___x_5333_; 
v_a_5332_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5332_);
lean_dec_ref_known(v___x_5329_, 1);
v___x_5333_ = lean_expr_eqv(v_a_5328_, v_a_5332_);
lean_dec(v_a_5328_);
if (v___x_5333_ == 0)
{
lean_object* v___x_5334_; 
lean_dec(v___x_5318_);
v___x_5334_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5317_, v_fvarId_5319_, v_a_5332_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
return v___x_5334_;
}
else
{
lean_object* v___x_5335_; 
lean_inc(v_mvarId_5317_);
v___x_5335_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_5318_, v_mvarId_5317_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v___x_5336_; 
lean_dec_ref_known(v___x_5335_, 1);
v___x_5336_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_5317_, v_fvarId_5319_, v_a_5332_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
return v___x_5336_;
}
else
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5344_; 
lean_dec(v_a_5332_);
lean_dec(v_fvarId_5319_);
lean_dec(v_mvarId_5317_);
v_a_5337_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5339_ = v___x_5335_;
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5335_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5342_; 
if (v_isShared_5340_ == 0)
{
v___x_5342_ = v___x_5339_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5337_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
}
}
}
else
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5352_; 
lean_dec(v_a_5328_);
lean_dec(v_fvarId_5319_);
lean_dec(v___x_5318_);
lean_dec(v_mvarId_5317_);
v_a_5345_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5347_ = v___x_5329_;
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5329_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v___x_5350_; 
if (v_isShared_5348_ == 0)
{
v___x_5350_ = v___x_5347_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_a_5345_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
else
{
lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5360_; 
lean_dec(v_fvarId_5319_);
lean_dec(v___x_5318_);
lean_dec(v_mvarId_5317_);
v_a_5353_ = lean_ctor_get(v___x_5327_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5355_ = v___x_5327_;
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5327_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5358_; 
if (v_isShared_5356_ == 0)
{
v___x_5358_ = v___x_5355_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5353_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
else
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5368_; 
lean_dec(v_fvarId_5319_);
lean_dec(v___x_5318_);
lean_dec(v_mvarId_5317_);
v_a_5361_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5326_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5326_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5366_; 
if (v_isShared_5364_ == 0)
{
v___x_5366_ = v___x_5363_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5369_, lean_object* v___x_5370_, lean_object* v_fvarId_5371_, lean_object* v_failIfUnchanged_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5378_; lean_object* v_res_5379_; 
v_failIfUnchanged_boxed_5378_ = lean_unbox(v_failIfUnchanged_5372_);
v_res_5379_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5369_, v___x_5370_, v_fvarId_5371_, v_failIfUnchanged_boxed_5378_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
lean_dec(v___y_5376_);
lean_dec_ref(v___y_5375_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5380_, lean_object* v_fvarId_5381_, uint8_t v_failIfUnchanged_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_){
_start:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___f_5390_; lean_object* v___x_5391_; 
v___x_5388_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5389_ = lean_box(v_failIfUnchanged_5382_);
lean_inc(v_mvarId_5380_);
v___f_5390_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5390_, 0, v_mvarId_5380_);
lean_closure_set(v___f_5390_, 1, v___x_5388_);
lean_closure_set(v___f_5390_, 2, v_fvarId_5381_);
lean_closure_set(v___f_5390_, 3, v___x_5389_);
v___x_5391_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5380_, v___f_5390_, v_a_5383_, v_a_5384_, v_a_5385_, v_a_5386_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5392_, lean_object* v_fvarId_5393_, lean_object* v_failIfUnchanged_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5400_; lean_object* v_res_5401_; 
v_failIfUnchanged_boxed_5400_ = lean_unbox(v_failIfUnchanged_5394_);
v_res_5401_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5392_, v_fvarId_5393_, v_failIfUnchanged_boxed_5400_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_);
lean_dec(v_a_5398_);
lean_dec_ref(v_a_5397_);
lean_dec(v_a_5396_);
lean_dec_ref(v_a_5395_);
return v_res_5401_;
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
