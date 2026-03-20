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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4_value;
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
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
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
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_binderName_107_);
return v___x_113_;
}
}
else
{
lean_del_object(v___x_117_);
lean_dec(v_val_115_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
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
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
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
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
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
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
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
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
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
v___x_987_ = lean_apply_8(v_x_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_x_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg___lam__0(v_x_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__1___redArg(lean_object* v_decls_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_1009_; 
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
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg___boxed(lean_object* v_decls_1076_, lean_object* v_k_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1076_, v_k_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
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
v___x_1110_ = lean_apply_8(v_k_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, lean_box(0));
return v___x_1110_;
}
}
else
{
lean_object* v___x_1111_; 
lean_dec(v___x_1097_);
lean_dec(v_fvarId_1087_);
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
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext(lean_object* v_00_u03b1_1123_, lean_object* v_fvarId_1124_, lean_object* v_k_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v_fvarId_1124_, v_k_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withDeclInContext___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_fvarId_1136_, lean_object* v_k_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Meta_ExtractLets_withDeclInContext(v_00_u03b1_1135_, v_fvarId_1136_, v_k_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
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
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(lean_object* v_00_u03b1_1171_, lean_object* v_decls_1172_, lean_object* v_k_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___redArg(v_decls_1172_, v_k_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_decls_1184_, lean_object* v_k_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(v_00_u03b1_1183_, v_decls_1184_, v_k_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
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
size_t v_x_12250__boxed_1604_; size_t v_x_12251__boxed_1605_; lean_object* v_res_1606_; 
v_x_12250__boxed_1604_ = lean_unbox_usize(v_x_1594_);
lean_dec(v_x_1594_);
v_x_12251__boxed_1605_ = lean_unbox_usize(v_x_1595_);
lean_dec(v_x_1595_);
v_res_1606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_1593_, v_x_12250__boxed_1604_, v_x_12251__boxed_1605_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
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
v___x_1734_ = lean_apply_9(v_k_1724_, v_b_1728_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, lean_box(0));
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(lean_object* v_k_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v_b_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(lean_object* v_name_1746_, uint8_t v_bi_1747_, lean_object* v_type_1748_, lean_object* v_k_1749_, uint8_t v_kind_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___f_1759_; lean_object* v___x_1760_; 
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
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__4(uint8_t v_types_1817_, lean_object* v_e_1818_, lean_object* v___f_1819_, lean_object* v_____r_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
if (v_types_1817_ == 0)
{
lean_object* v___x_1829_; 
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
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
v___x_1836_ = lean_apply_9(v___f_1819_, v___x_1835_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, lean_box(0));
return v___x_1836_;
}
else
{
lean_object* v___x_1838_; 
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
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
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
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
return v_res_1864_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(lean_object* v_msg_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v_toApplicative_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1945_; 
v___x_1879_ = lean_obj_once(&l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0, &l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0);
v___x_1880_ = l_ReaderT_instMonad___redArg(v___x_1879_);
v_toApplicative_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1880_, 1);
lean_dec(v_unused_1946_);
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1945_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_toApplicative_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1945_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_toFunctor_1885_; lean_object* v_toSeq_1886_; lean_object* v_toSeqLeft_1887_; lean_object* v_toSeqRight_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1943_; 
v_toFunctor_1885_ = lean_ctor_get(v_toApplicative_1881_, 0);
v_toSeq_1886_ = lean_ctor_get(v_toApplicative_1881_, 2);
v_toSeqLeft_1887_ = lean_ctor_get(v_toApplicative_1881_, 3);
v_toSeqRight_1888_ = lean_ctor_get(v_toApplicative_1881_, 4);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_toApplicative_1881_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v_toApplicative_1881_, 1);
lean_dec(v_unused_1944_);
v___x_1890_ = v_toApplicative_1881_;
v_isShared_1891_ = v_isSharedCheck_1943_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_toSeqRight_1888_);
lean_inc(v_toSeqLeft_1887_);
lean_inc(v_toSeq_1886_);
lean_inc(v_toFunctor_1885_);
lean_dec(v_toApplicative_1881_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1943_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___f_1892_; lean_object* v___f_1893_; lean_object* v___f_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___f_1897_; lean_object* v___f_1898_; lean_object* v___f_1899_; lean_object* v___x_1901_; 
v___f_1892_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1));
v___f_1893_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2));
lean_inc_ref(v_toFunctor_1885_);
v___f_1894_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1894_, 0, v_toFunctor_1885_);
v___f_1895_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1895_, 0, v_toFunctor_1885_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___f_1894_);
lean_ctor_set(v___x_1896_, 1, v___f_1895_);
v___f_1897_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1897_, 0, v_toSeqRight_1888_);
v___f_1898_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1898_, 0, v_toSeqLeft_1887_);
v___f_1899_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1899_, 0, v_toSeq_1886_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 4, v___f_1897_);
lean_ctor_set(v___x_1890_, 3, v___f_1898_);
lean_ctor_set(v___x_1890_, 2, v___f_1899_);
lean_ctor_set(v___x_1890_, 1, v___f_1892_);
lean_ctor_set(v___x_1890_, 0, v___x_1896_);
v___x_1901_ = v___x_1890_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v___f_1892_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v___f_1899_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v___f_1898_);
lean_ctor_set(v_reuseFailAlloc_1942_, 4, v___f_1897_);
v___x_1901_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1903_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v___f_1893_);
lean_ctor_set(v___x_1883_, 0, v___x_1901_);
v___x_1903_ = v___x_1883_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___f_1893_);
v___x_1903_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v_toApplicative_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1939_; 
v___x_1904_ = l_ReaderT_instMonad___redArg(v___x_1903_);
v_toApplicative_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1904_, 1);
lean_dec(v_unused_1940_);
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1939_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_toApplicative_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1939_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_toFunctor_1909_; lean_object* v_toSeq_1910_; lean_object* v_toSeqLeft_1911_; lean_object* v_toSeqRight_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1937_; 
v_toFunctor_1909_ = lean_ctor_get(v_toApplicative_1905_, 0);
v_toSeq_1910_ = lean_ctor_get(v_toApplicative_1905_, 2);
v_toSeqLeft_1911_ = lean_ctor_get(v_toApplicative_1905_, 3);
v_toSeqRight_1912_ = lean_ctor_get(v_toApplicative_1905_, 4);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_toApplicative_1905_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_toApplicative_1905_, 1);
lean_dec(v_unused_1938_);
v___x_1914_ = v_toApplicative_1905_;
v_isShared_1915_ = v_isSharedCheck_1937_;
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
v_isShared_1915_ = v_isSharedCheck_1937_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___f_1916_; lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___f_1921_; lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___x_1925_; 
v___f_1916_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3));
v___f_1917_ = ((lean_object*)(l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4));
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
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___f_1916_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v___f_1923_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v___f_1922_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v___f_1921_);
v___x_1925_ = v_reuseFailAlloc_1936_;
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
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___f_1917_);
v___x_1927_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_49287__overap_1933_; lean_object* v___x_1934_; 
v___x_1928_ = l_ReaderT_instMonad___redArg(v___x_1927_);
v___x_1929_ = l_ReaderT_instMonad___redArg(v___x_1928_);
v___x_1930_ = l_Lean_instInhabitedExpr;
v___x_1931_ = l_instInhabitedOfMonad___redArg(v___x_1929_, v___x_1930_);
v___f_1932_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1932_, 0, v___x_1931_);
v___x_49287__overap_1933_ = lean_panic_fn(v___f_1932_, v_msg_1870_);
v___x_1934_ = lean_apply_8(v___x_49287__overap_1933_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, lean_box(0));
return v___x_1934_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(lean_object* v_msg_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v_msg_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0(lean_object* v_binderName_1957_, uint8_t v_binderInfo_1958_, lean_object* v_e_1959_, lean_object* v_binderType_1960_, lean_object* v_body_1961_, lean_object* v_t_1962_, lean_object* v_b_1963_){
_start:
{
uint8_t v___y_1965_; size_t v___x_1969_; size_t v___x_1970_; uint8_t v___x_1971_; 
v___x_1969_ = lean_ptr_addr(v_binderType_1960_);
v___x_1970_ = lean_ptr_addr(v_t_1962_);
v___x_1971_ = lean_usize_dec_eq(v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
v___y_1965_ = v___x_1971_;
goto v___jp_1964_;
}
else
{
size_t v___x_1972_; size_t v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = lean_ptr_addr(v_body_1961_);
v___x_1973_ = lean_ptr_addr(v_b_1963_);
v___x_1974_ = lean_usize_dec_eq(v___x_1972_, v___x_1973_);
v___y_1965_ = v___x_1974_;
goto v___jp_1964_;
}
v___jp_1964_:
{
if (v___y_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Expr_lam___override(v_binderName_1957_, v_t_1962_, v_b_1963_, v_binderInfo_1958_);
return v___x_1966_;
}
else
{
uint8_t v___x_1967_; 
v___x_1967_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1958_, v_binderInfo_1958_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Expr_lam___override(v_binderName_1957_, v_t_1962_, v_b_1963_, v_binderInfo_1958_);
return v___x_1968_;
}
else
{
lean_dec_ref(v_b_1963_);
lean_dec_ref(v_t_1962_);
lean_dec(v_binderName_1957_);
lean_inc_ref(v_e_1959_);
return v_e_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(lean_object* v_binderName_1975_, lean_object* v_binderInfo_1976_, lean_object* v_e_1977_, lean_object* v_binderType_1978_, lean_object* v_body_1979_, lean_object* v_t_1980_, lean_object* v_b_1981_){
_start:
{
uint8_t v_binderInfo_52547__boxed_1982_; lean_object* v_res_1983_; 
v_binderInfo_52547__boxed_1982_ = lean_unbox(v_binderInfo_1976_);
v_res_1983_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(v_binderName_1975_, v_binderInfo_52547__boxed_1982_, v_e_1977_, v_binderType_1978_, v_body_1979_, v_t_1980_, v_b_1981_);
lean_dec_ref(v_body_1979_);
lean_dec_ref(v_binderType_1978_);
lean_dec_ref(v_e_1977_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1(lean_object* v_binderName_1984_, uint8_t v_binderInfo_1985_, lean_object* v_e_1986_, lean_object* v_binderType_1987_, lean_object* v_body_1988_, lean_object* v_t_1989_, lean_object* v_b_1990_){
_start:
{
uint8_t v___y_1992_; size_t v___x_1996_; size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_ptr_addr(v_binderType_1987_);
v___x_1997_ = lean_ptr_addr(v_t_1989_);
v___x_1998_ = lean_usize_dec_eq(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
v___y_1992_ = v___x_1998_;
goto v___jp_1991_;
}
else
{
size_t v___x_1999_; size_t v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = lean_ptr_addr(v_body_1988_);
v___x_2000_ = lean_ptr_addr(v_b_1990_);
v___x_2001_ = lean_usize_dec_eq(v___x_1999_, v___x_2000_);
v___y_1992_ = v___x_2001_;
goto v___jp_1991_;
}
v___jp_1991_:
{
if (v___y_1992_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Expr_forallE___override(v_binderName_1984_, v_t_1989_, v_b_1990_, v_binderInfo_1985_);
return v___x_1993_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1985_, v_binderInfo_1985_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Expr_forallE___override(v_binderName_1984_, v_t_1989_, v_b_1990_, v_binderInfo_1985_);
return v___x_1995_;
}
else
{
lean_dec_ref(v_b_1990_);
lean_dec_ref(v_t_1989_);
lean_dec(v_binderName_1984_);
lean_inc_ref(v_e_1986_);
return v_e_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(lean_object* v_binderName_2002_, lean_object* v_binderInfo_2003_, lean_object* v_e_2004_, lean_object* v_binderType_2005_, lean_object* v_body_2006_, lean_object* v_t_2007_, lean_object* v_b_2008_){
_start:
{
uint8_t v_binderInfo_52581__boxed_2009_; lean_object* v_res_2010_; 
v_binderInfo_52581__boxed_2009_ = lean_unbox(v_binderInfo_2003_);
v_res_2010_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(v_binderName_2002_, v_binderInfo_52581__boxed_2009_, v_e_2004_, v_binderType_2005_, v_body_2006_, v_t_2007_, v_b_2008_);
lean_dec_ref(v_body_2006_);
lean_dec_ref(v_binderType_2005_);
lean_dec_ref(v_e_2004_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(lean_object* v_name_2011_, lean_object* v_type_2012_, lean_object* v_val_2013_, lean_object* v_k_2014_, uint8_t v_nondep_2015_, uint8_t v_kind_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___f_2025_; lean_object* v___x_2026_; 
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2025_, 0, v_k_2014_);
lean_closure_set(v___f_2025_, 1, v___y_2017_);
lean_closure_set(v___f_2025_, 2, v___y_2018_);
lean_closure_set(v___f_2025_, 3, v___y_2019_);
v___x_2026_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2011_, v_type_2012_, v_val_2013_, v___f_2025_, v_nondep_2015_, v_kind_2016_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
if (lean_obj_tag(v___x_2026_) == 0)
{
return v___x_2026_;
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(lean_object* v_name_2035_, lean_object* v_type_2036_, lean_object* v_val_2037_, lean_object* v_k_2038_, lean_object* v_nondep_2039_, lean_object* v_kind_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v_nondep_boxed_2049_; uint8_t v_kind_boxed_2050_; lean_object* v_res_2051_; 
v_nondep_boxed_2049_ = lean_unbox(v_nondep_2039_);
v_kind_boxed_2050_ = lean_unbox(v_kind_2040_);
v_res_2051_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_2035_, v_type_2036_, v_val_2037_, v_k_2038_, v_nondep_boxed_2049_, v_kind_boxed_2050_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(lean_object* v_msg_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = l_Lean_instInhabitedExpr;
v___x_2054_ = lean_panic_fn(v___x_2053_, v_msg_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(lean_object* v_a_2055_, lean_object* v_x_2056_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
else
{
lean_object* v_key_2058_; lean_object* v_value_2059_; lean_object* v_tail_2060_; uint8_t v___x_2061_; 
v_key_2058_ = lean_ctor_get(v_x_2056_, 0);
v_value_2059_ = lean_ctor_get(v_x_2056_, 1);
v_tail_2060_ = lean_ctor_get(v_x_2056_, 2);
v___x_2061_ = l_Lean_ExprStructEq_beq(v_key_2058_, v_a_2055_);
if (v___x_2061_ == 0)
{
v_x_2056_ = v_tail_2060_;
goto _start;
}
else
{
lean_object* v___x_2063_; 
lean_inc(v_value_2059_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_value_2059_);
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(lean_object* v_a_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2064_, v_x_2065_);
lean_dec(v_x_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(lean_object* v_m_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_buckets_2069_; lean_object* v___x_2070_; uint64_t v___x_2071_; uint64_t v___x_2072_; uint64_t v___x_2073_; uint64_t v_fold_2074_; uint64_t v___x_2075_; uint64_t v___x_2076_; uint64_t v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_buckets_2069_ = lean_ctor_get(v_m_2067_, 1);
v___x_2070_ = lean_array_get_size(v_buckets_2069_);
v___x_2071_ = l_Lean_ExprStructEq_hash(v_a_2068_);
v___x_2072_ = 32ULL;
v___x_2073_ = lean_uint64_shift_right(v___x_2071_, v___x_2072_);
v_fold_2074_ = lean_uint64_xor(v___x_2071_, v___x_2073_);
v___x_2075_ = 16ULL;
v___x_2076_ = lean_uint64_shift_right(v_fold_2074_, v___x_2075_);
v___x_2077_ = lean_uint64_xor(v_fold_2074_, v___x_2076_);
v___x_2078_ = lean_uint64_to_usize(v___x_2077_);
v___x_2079_ = lean_usize_of_nat(v___x_2070_);
v___x_2080_ = ((size_t)1ULL);
v___x_2081_ = lean_usize_sub(v___x_2079_, v___x_2080_);
v___x_2082_ = lean_usize_land(v___x_2078_, v___x_2081_);
v___x_2083_ = lean_array_uget_borrowed(v_buckets_2069_, v___x_2082_);
v___x_2084_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_2068_, v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(lean_object* v_m_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_2085_, v_a_2086_);
lean_dec_ref(v_a_2086_);
lean_dec_ref(v_m_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(lean_object* v_a_2088_, lean_object* v_x_2089_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 0)
{
uint8_t v___x_2090_; 
v___x_2090_ = 0;
return v___x_2090_;
}
else
{
lean_object* v_key_2091_; lean_object* v_tail_2092_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; lean_object* v_fst_2095_; lean_object* v_snd_2096_; uint8_t v___x_2100_; 
v_key_2091_ = lean_ctor_get(v_x_2089_, 0);
v_tail_2092_ = lean_ctor_get(v_x_2089_, 2);
v_fst_2093_ = lean_ctor_get(v_key_2091_, 0);
v_snd_2094_ = lean_ctor_get(v_key_2091_, 1);
v_fst_2095_ = lean_ctor_get(v_a_2088_, 0);
v_snd_2096_ = lean_ctor_get(v_a_2088_, 1);
v___x_2100_ = lean_unbox(v_fst_2093_);
if (v___x_2100_ == 0)
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_unbox(v_fst_2095_);
if (v___x_2101_ == 0)
{
goto v___jp_2097_;
}
else
{
v_x_2089_ = v_tail_2092_;
goto _start;
}
}
else
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_unbox(v_fst_2095_);
if (v___x_2103_ == 0)
{
v_x_2089_ = v_tail_2092_;
goto _start;
}
else
{
goto v___jp_2097_;
}
}
v___jp_2097_:
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Lean_ExprStructEq_beq(v_snd_2094_, v_snd_2096_);
if (v___x_2098_ == 0)
{
v_x_2089_ = v_tail_2092_;
goto _start;
}
else
{
return v___x_2098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(lean_object* v_a_2105_, lean_object* v_x_2106_){
_start:
{
uint8_t v_res_2107_; lean_object* v_r_2108_; 
v_res_2107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2105_, v_x_2106_);
lean_dec(v_x_2106_);
lean_dec_ref(v_a_2105_);
v_r_2108_ = lean_box(v_res_2107_);
return v_r_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(lean_object* v_a_2109_, lean_object* v_b_2110_, lean_object* v_x_2111_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_dec(v_b_2110_);
lean_dec_ref(v_a_2109_);
return v_x_2111_;
}
else
{
lean_object* v_key_2112_; lean_object* v_value_2113_; lean_object* v_tail_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2133_; 
v_key_2112_ = lean_ctor_get(v_x_2111_, 0);
v_value_2113_ = lean_ctor_get(v_x_2111_, 1);
v_tail_2114_ = lean_ctor_get(v_x_2111_, 2);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_x_2111_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2116_ = v_x_2111_;
v_isShared_2117_ = v_isSharedCheck_2133_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_tail_2114_);
lean_inc(v_value_2113_);
lean_inc(v_key_2112_);
lean_dec(v_x_2111_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2133_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v_fst_2123_; lean_object* v_snd_2124_; lean_object* v_fst_2125_; lean_object* v_snd_2126_; uint8_t v___x_2130_; 
v_fst_2123_ = lean_ctor_get(v_key_2112_, 0);
v_snd_2124_ = lean_ctor_get(v_key_2112_, 1);
v_fst_2125_ = lean_ctor_get(v_a_2109_, 0);
v_snd_2126_ = lean_ctor_get(v_a_2109_, 1);
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
goto v___jp_2118_;
}
}
else
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_unbox(v_fst_2125_);
if (v___x_2132_ == 0)
{
goto v___jp_2118_;
}
else
{
goto v___jp_2127_;
}
}
v___jp_2118_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2109_, v_b_2110_, v_tail_2114_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 2, v___x_2119_);
v___x_2121_ = v___x_2116_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_key_2112_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_value_2113_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
v___jp_2127_:
{
uint8_t v___x_2128_; 
v___x_2128_ = l_Lean_ExprStructEq_beq(v_snd_2124_, v_snd_2126_);
if (v___x_2128_ == 0)
{
goto v___jp_2118_;
}
else
{
lean_object* v___x_2129_; 
lean_del_object(v___x_2116_);
lean_dec(v_value_2113_);
lean_dec(v_key_2112_);
v___x_2129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2129_, 0, v_a_2109_);
lean_ctor_set(v___x_2129_, 1, v_b_2110_);
lean_ctor_set(v___x_2129_, 2, v_tail_2114_);
return v___x_2129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
return v_x_2134_;
}
else
{
lean_object* v_key_2136_; lean_object* v_value_2137_; lean_object* v_tail_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2169_; 
v_key_2136_ = lean_ctor_get(v_x_2135_, 0);
v_value_2137_ = lean_ctor_get(v_x_2135_, 1);
v_tail_2138_ = lean_ctor_get(v_x_2135_, 2);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_x_2135_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2140_ = v_x_2135_;
v_isShared_2141_ = v_isSharedCheck_2169_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_tail_2138_);
lean_inc(v_value_2137_);
lean_inc(v_key_2136_);
lean_dec(v_x_2135_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2169_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v___x_2144_; uint64_t v___y_2146_; uint8_t v___x_2166_; 
v_fst_2142_ = lean_ctor_get(v_key_2136_, 0);
v_snd_2143_ = lean_ctor_get(v_key_2136_, 1);
v___x_2144_ = lean_array_get_size(v_x_2134_);
v___x_2166_ = lean_unbox(v_fst_2142_);
if (v___x_2166_ == 0)
{
uint64_t v___x_2167_; 
v___x_2167_ = 13ULL;
v___y_2146_ = v___x_2167_;
goto v___jp_2145_;
}
else
{
uint64_t v___x_2168_; 
v___x_2168_ = 11ULL;
v___y_2146_ = v___x_2168_;
goto v___jp_2145_;
}
v___jp_2145_:
{
uint64_t v___x_2147_; uint64_t v___x_2148_; uint64_t v___x_2149_; uint64_t v___x_2150_; uint64_t v_fold_2151_; uint64_t v___x_2152_; uint64_t v___x_2153_; uint64_t v___x_2154_; size_t v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2147_ = l_Lean_ExprStructEq_hash(v_snd_2143_);
v___x_2148_ = lean_uint64_mix_hash(v___y_2146_, v___x_2147_);
v___x_2149_ = 32ULL;
v___x_2150_ = lean_uint64_shift_right(v___x_2148_, v___x_2149_);
v_fold_2151_ = lean_uint64_xor(v___x_2148_, v___x_2150_);
v___x_2152_ = 16ULL;
v___x_2153_ = lean_uint64_shift_right(v_fold_2151_, v___x_2152_);
v___x_2154_ = lean_uint64_xor(v_fold_2151_, v___x_2153_);
v___x_2155_ = lean_uint64_to_usize(v___x_2154_);
v___x_2156_ = lean_usize_of_nat(v___x_2144_);
v___x_2157_ = ((size_t)1ULL);
v___x_2158_ = lean_usize_sub(v___x_2156_, v___x_2157_);
v___x_2159_ = lean_usize_land(v___x_2155_, v___x_2158_);
v___x_2160_ = lean_array_uget_borrowed(v_x_2134_, v___x_2159_);
lean_inc(v___x_2160_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 2, v___x_2160_);
v___x_2162_ = v___x_2140_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_key_2136_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_value_2137_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_array_uset(v_x_2134_, v___x_2159_, v___x_2162_);
v_x_2134_ = v___x_2163_;
v_x_2135_ = v_tail_2138_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(lean_object* v_i_2170_, lean_object* v_source_2171_, lean_object* v_target_2172_){
_start:
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_array_get_size(v_source_2171_);
v___x_2174_ = lean_nat_dec_lt(v_i_2170_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec_ref(v_source_2171_);
lean_dec(v_i_2170_);
return v_target_2172_;
}
else
{
lean_object* v_es_2175_; lean_object* v___x_2176_; lean_object* v_source_2177_; lean_object* v_target_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v_es_2175_ = lean_array_fget(v_source_2171_, v_i_2170_);
v___x_2176_ = lean_box(0);
v_source_2177_ = lean_array_fset(v_source_2171_, v_i_2170_, v___x_2176_);
v_target_2178_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_2172_, v_es_2175_);
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_add(v_i_2170_, v___x_2179_);
lean_dec(v_i_2170_);
v_i_2170_ = v___x_2180_;
v_source_2171_ = v_source_2177_;
v_target_2172_ = v_target_2178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(lean_object* v_data_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v_nbuckets_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2183_ = lean_array_get_size(v_data_2182_);
v___x_2184_ = lean_unsigned_to_nat(2u);
v_nbuckets_2185_ = lean_nat_mul(v___x_2183_, v___x_2184_);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_box(0);
v___x_2188_ = lean_mk_array(v_nbuckets_2185_, v___x_2187_);
v___x_2189_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_2186_, v_data_2182_, v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(lean_object* v_m_2190_, lean_object* v_a_2191_, lean_object* v_b_2192_){
_start:
{
lean_object* v_size_2193_; lean_object* v_buckets_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2245_; 
v_size_2193_ = lean_ctor_get(v_m_2190_, 0);
v_buckets_2194_ = lean_ctor_get(v_m_2190_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_m_2190_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2196_ = v_m_2190_;
v_isShared_2197_ = v_isSharedCheck_2245_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_buckets_2194_);
lean_inc(v_size_2193_);
lean_dec(v_m_2190_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2245_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_fst_2198_; lean_object* v_snd_2199_; lean_object* v___x_2200_; uint64_t v___y_2202_; uint8_t v___x_2242_; 
v_fst_2198_ = lean_ctor_get(v_a_2191_, 0);
v_snd_2199_ = lean_ctor_get(v_a_2191_, 1);
v___x_2200_ = lean_array_get_size(v_buckets_2194_);
v___x_2242_ = lean_unbox(v_fst_2198_);
if (v___x_2242_ == 0)
{
uint64_t v___x_2243_; 
v___x_2243_ = 13ULL;
v___y_2202_ = v___x_2243_;
goto v___jp_2201_;
}
else
{
uint64_t v___x_2244_; 
v___x_2244_ = 11ULL;
v___y_2202_ = v___x_2244_;
goto v___jp_2201_;
}
v___jp_2201_:
{
uint64_t v___x_2203_; uint64_t v___x_2204_; uint64_t v___x_2205_; uint64_t v___x_2206_; uint64_t v_fold_2207_; uint64_t v___x_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; lean_object* v_bkt_2216_; uint8_t v___x_2217_; 
v___x_2203_ = l_Lean_ExprStructEq_hash(v_snd_2199_);
v___x_2204_ = lean_uint64_mix_hash(v___y_2202_, v___x_2203_);
v___x_2205_ = 32ULL;
v___x_2206_ = lean_uint64_shift_right(v___x_2204_, v___x_2205_);
v_fold_2207_ = lean_uint64_xor(v___x_2204_, v___x_2206_);
v___x_2208_ = 16ULL;
v___x_2209_ = lean_uint64_shift_right(v_fold_2207_, v___x_2208_);
v___x_2210_ = lean_uint64_xor(v_fold_2207_, v___x_2209_);
v___x_2211_ = lean_uint64_to_usize(v___x_2210_);
v___x_2212_ = lean_usize_of_nat(v___x_2200_);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_sub(v___x_2212_, v___x_2213_);
v___x_2215_ = lean_usize_land(v___x_2211_, v___x_2214_);
v_bkt_2216_ = lean_array_uget_borrowed(v_buckets_2194_, v___x_2215_);
v___x_2217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_2191_, v_bkt_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v_size_x27_2219_; lean_object* v___x_2220_; lean_object* v_buckets_x27_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2218_ = lean_unsigned_to_nat(1u);
v_size_x27_2219_ = lean_nat_add(v_size_2193_, v___x_2218_);
lean_dec(v_size_2193_);
lean_inc(v_bkt_2216_);
v___x_2220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2220_, 0, v_a_2191_);
lean_ctor_set(v___x_2220_, 1, v_b_2192_);
lean_ctor_set(v___x_2220_, 2, v_bkt_2216_);
v_buckets_x27_2221_ = lean_array_uset(v_buckets_2194_, v___x_2215_, v___x_2220_);
v___x_2222_ = lean_unsigned_to_nat(4u);
v___x_2223_ = lean_nat_mul(v_size_x27_2219_, v___x_2222_);
v___x_2224_ = lean_unsigned_to_nat(3u);
v___x_2225_ = lean_nat_div(v___x_2223_, v___x_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_array_get_size(v_buckets_x27_2221_);
v___x_2227_ = lean_nat_dec_le(v___x_2225_, v___x_2226_);
lean_dec(v___x_2225_);
if (v___x_2227_ == 0)
{
lean_object* v_val_2228_; lean_object* v___x_2230_; 
v_val_2228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_2221_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v_val_2228_);
lean_ctor_set(v___x_2196_, 0, v_size_x27_2219_);
v___x_2230_ = v___x_2196_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_size_x27_2219_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_val_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
else
{
lean_object* v___x_2233_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v_buckets_x27_2221_);
lean_ctor_set(v___x_2196_, 0, v_size_x27_2219_);
v___x_2233_ = v___x_2196_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_size_x27_2219_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_buckets_x27_2221_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v___x_2235_; lean_object* v_buckets_x27_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_inc(v_bkt_2216_);
v___x_2235_ = lean_box(0);
v_buckets_x27_2236_ = lean_array_uset(v_buckets_2194_, v___x_2215_, v___x_2235_);
v___x_2237_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_2191_, v_b_2192_, v_bkt_2216_);
v___x_2238_ = lean_array_uset(v_buckets_x27_2236_, v___x_2215_, v___x_2237_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v___x_2238_);
v___x_2240_ = v___x_2196_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_size_2193_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(lean_object* v_a_2246_, lean_object* v_x_2247_){
_start:
{
if (lean_obj_tag(v_x_2247_) == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_box(0);
return v___x_2248_;
}
else
{
lean_object* v_key_2249_; lean_object* v_value_2250_; lean_object* v_tail_2251_; lean_object* v_fst_2252_; lean_object* v_snd_2253_; lean_object* v_fst_2254_; lean_object* v_snd_2255_; uint8_t v___x_2260_; 
v_key_2249_ = lean_ctor_get(v_x_2247_, 0);
v_value_2250_ = lean_ctor_get(v_x_2247_, 1);
v_tail_2251_ = lean_ctor_get(v_x_2247_, 2);
v_fst_2252_ = lean_ctor_get(v_key_2249_, 0);
v_snd_2253_ = lean_ctor_get(v_key_2249_, 1);
v_fst_2254_ = lean_ctor_get(v_a_2246_, 0);
v_snd_2255_ = lean_ctor_get(v_a_2246_, 1);
v___x_2260_ = lean_unbox(v_fst_2252_);
if (v___x_2260_ == 0)
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_unbox(v_fst_2254_);
if (v___x_2261_ == 0)
{
goto v___jp_2256_;
}
else
{
v_x_2247_ = v_tail_2251_;
goto _start;
}
}
else
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_unbox(v_fst_2254_);
if (v___x_2263_ == 0)
{
v_x_2247_ = v_tail_2251_;
goto _start;
}
else
{
goto v___jp_2256_;
}
}
v___jp_2256_:
{
uint8_t v___x_2257_; 
v___x_2257_ = l_Lean_ExprStructEq_beq(v_snd_2253_, v_snd_2255_);
if (v___x_2257_ == 0)
{
v_x_2247_ = v_tail_2251_;
goto _start;
}
else
{
lean_object* v___x_2259_; 
lean_inc(v_value_2250_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_value_2250_);
return v___x_2259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(lean_object* v_a_2265_, lean_object* v_x_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2265_, v_x_2266_);
lean_dec(v_x_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(lean_object* v_m_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_buckets_2270_; lean_object* v_fst_2271_; lean_object* v_snd_2272_; lean_object* v___x_2273_; uint64_t v___y_2275_; uint8_t v___x_2291_; 
v_buckets_2270_ = lean_ctor_get(v_m_2268_, 1);
v_fst_2271_ = lean_ctor_get(v_a_2269_, 0);
v_snd_2272_ = lean_ctor_get(v_a_2269_, 1);
v___x_2273_ = lean_array_get_size(v_buckets_2270_);
v___x_2291_ = lean_unbox(v_fst_2271_);
if (v___x_2291_ == 0)
{
uint64_t v___x_2292_; 
v___x_2292_ = 13ULL;
v___y_2275_ = v___x_2292_;
goto v___jp_2274_;
}
else
{
uint64_t v___x_2293_; 
v___x_2293_ = 11ULL;
v___y_2275_ = v___x_2293_;
goto v___jp_2274_;
}
v___jp_2274_:
{
uint64_t v___x_2276_; uint64_t v___x_2277_; uint64_t v___x_2278_; uint64_t v___x_2279_; uint64_t v_fold_2280_; uint64_t v___x_2281_; uint64_t v___x_2282_; uint64_t v___x_2283_; size_t v___x_2284_; size_t v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2276_ = l_Lean_ExprStructEq_hash(v_snd_2272_);
v___x_2277_ = lean_uint64_mix_hash(v___y_2275_, v___x_2276_);
v___x_2278_ = 32ULL;
v___x_2279_ = lean_uint64_shift_right(v___x_2277_, v___x_2278_);
v_fold_2280_ = lean_uint64_xor(v___x_2277_, v___x_2279_);
v___x_2281_ = 16ULL;
v___x_2282_ = lean_uint64_shift_right(v_fold_2280_, v___x_2281_);
v___x_2283_ = lean_uint64_xor(v_fold_2280_, v___x_2282_);
v___x_2284_ = lean_uint64_to_usize(v___x_2283_);
v___x_2285_ = lean_usize_of_nat(v___x_2273_);
v___x_2286_ = ((size_t)1ULL);
v___x_2287_ = lean_usize_sub(v___x_2285_, v___x_2286_);
v___x_2288_ = lean_usize_land(v___x_2284_, v___x_2287_);
v___x_2289_ = lean_array_uget_borrowed(v_buckets_2270_, v___x_2288_);
v___x_2290_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_2269_, v___x_2289_);
return v___x_2290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(lean_object* v_m_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_2294_, v_a_2295_);
lean_dec_ref(v_a_2295_);
lean_dec_ref(v_m_2294_);
return v_res_2296_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2297_; lean_object* v_dummy_2298_; 
v___x_2297_ = lean_box(0);
v_dummy_2298_ = l_Lean_Expr_sort___override(v___x_2297_);
return v_dummy_2298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(lean_object* v_upperBound_2299_, lean_object* v_fst_2300_, lean_object* v_fvars_2301_, lean_object* v_a_2302_, lean_object* v_b_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_a_2313_; uint8_t v___x_2317_; 
v___x_2317_ = lean_nat_dec_lt(v_a_2302_, v_upperBound_2299_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v_a_2302_);
lean_dec(v_fvars_2301_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_b_2303_);
return v___x_2318_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v_binderInfo_2321_; uint8_t v___x_2322_; 
v___x_2319_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
v___x_2320_ = lean_array_get_borrowed(v___x_2319_, v_fst_2300_, v_a_2302_);
v_binderInfo_2321_ = lean_ctor_get_uint8(v___x_2320_, sizeof(void*)*2);
v___x_2322_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2321_);
if (v___x_2322_ == 0)
{
v_a_2313_ = v_b_2303_;
goto v___jp_2312_;
}
else
{
uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2323_ = 0;
v___x_2324_ = l_Lean_instInhabitedExpr;
v___x_2325_ = lean_array_get_borrowed(v___x_2324_, v_b_2303_, v_a_2302_);
lean_inc(v___y_2310_);
lean_inc_ref(v___y_2309_);
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
lean_inc(v___y_2306_);
lean_inc(v___y_2305_);
lean_inc_ref(v___y_2304_);
lean_inc(v___x_2325_);
lean_inc(v_fvars_2301_);
v___x_2326_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2301_, v___x_2325_, v___x_2323_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = lean_array_set(v_b_2303_, v_a_2302_, v_a_2327_);
v_a_2313_ = v___x_2328_;
goto v___jp_2312_;
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_b_2303_);
lean_dec(v_a_2302_);
lean_dec(v_fvars_2301_);
v_a_2329_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2326_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2326_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
v___jp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = lean_nat_add(v_a_2302_, v___x_2314_);
lean_dec(v_a_2302_);
v_a_2302_ = v___x_2315_;
v_b_2303_ = v_a_2313_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(lean_object* v_fvars_2337_, size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_bs_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_usize_dec_lt(v_i_2339_, v_sz_2338_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v_fvars_2337_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_bs_2340_);
return v___x_2350_;
}
else
{
uint8_t v___x_2351_; lean_object* v_v_2352_; lean_object* v___x_2353_; 
v___x_2351_ = 0;
v_v_2352_ = lean_array_uget_borrowed(v_bs_2340_, v_i_2339_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
lean_inc(v_v_2352_);
lean_inc(v_fvars_2337_);
v___x_2353_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2337_, v_v_2352_, v___x_2351_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; lean_object* v_bs_x27_2356_; size_t v___x_2357_; size_t v___x_2358_; lean_object* v___x_2359_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v_bs_x27_2356_ = lean_array_uset(v_bs_2340_, v_i_2339_, v___x_2355_);
v___x_2357_ = ((size_t)1ULL);
v___x_2358_ = lean_usize_add(v_i_2339_, v___x_2357_);
v___x_2359_ = lean_array_uset(v_bs_x27_2356_, v_i_2339_, v_a_2354_);
v_i_2339_ = v___x_2358_;
v_bs_2340_ = v___x_2359_;
goto _start;
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_bs_2340_);
lean_dec(v_fvars_2337_);
v_a_2361_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2353_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2353_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(lean_object* v_fvars_2369_, lean_object* v_f_2370_, lean_object* v_args_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
uint8_t v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = 0;
lean_inc(v_a_2378_);
lean_inc_ref(v_a_2377_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
lean_inc(v_a_2374_);
lean_inc(v_a_2373_);
lean_inc_ref(v_a_2372_);
lean_inc_ref(v_f_2370_);
lean_inc(v_fvars_2369_);
v___x_2381_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2369_, v_f_2370_, v___x_2380_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2381_) == 0)
{
uint8_t v_implicits_2382_; 
v_implicits_2382_ = lean_ctor_get_uint8(v_a_2372_, 2);
if (v_implicits_2382_ == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_a_2383_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2381_);
lean_inc(v_a_2378_);
lean_inc_ref(v_a_2377_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
v___x_2384_ = lean_infer_type(v_f_2370_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref(v___x_2384_);
lean_inc(v_a_2378_);
lean_inc_ref(v_a_2377_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
v___x_2386_ = l_Lean_Meta_instantiateForallWithParamInfos(v_a_2385_, v_args_2371_, v___x_2380_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v_fst_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref(v___x_2386_);
v_fst_2388_ = lean_ctor_get(v_a_2387_, 0);
lean_inc(v_fst_2388_);
lean_dec(v_a_2387_);
v___x_2389_ = lean_array_get_size(v_args_2371_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_2389_, v_fst_2388_, v_fvars_2369_, v___x_2390_, v_args_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_fst_2388_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2400_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2396_ = l_Lean_mkAppN(v_a_2383_, v_a_2392_);
lean_dec(v_a_2392_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2396_);
v___x_2398_ = v___x_2394_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec(v_a_2383_);
v_a_2401_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2391_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2391_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_a_2383_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_args_2371_);
lean_dec(v_fvars_2369_);
v_a_2409_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2386_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2386_);
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
else
{
lean_dec(v_a_2383_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_args_2371_);
lean_dec(v_fvars_2369_);
return v___x_2384_;
}
}
else
{
lean_object* v_a_2417_; size_t v_sz_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
lean_dec_ref(v_f_2370_);
v_a_2417_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2381_);
v_sz_2418_ = lean_array_size(v_args_2371_);
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_2369_, v_sz_2418_, v___x_2419_, v_args_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = l_Lean_mkAppN(v_a_2417_, v_a_2421_);
lean_dec(v_a_2421_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2425_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_a_2417_);
v_a_2430_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2420_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2420_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
else
{
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_args_2371_);
lean_dec_ref(v_f_2370_);
lean_dec(v_fvars_2369_);
return v___x_2381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(lean_object* v_fvars_2438_, lean_object* v_f_2439_, lean_object* v_args_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(v_fvars_2438_, v_f_2439_, v_args_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(lean_object* v_fvars_2450_, lean_object* v_b_2451_, uint8_t v___x_2452_, lean_object* v_mk_2453_, lean_object* v_a_2454_, lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_inc_ref(v_x_2455_);
v___x_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_x_2455_);
lean_ctor_set(v___x_2464_, 1, v_fvars_2450_);
v___x_2465_ = lean_expr_instantiate1(v_b_2451_, v_x_2455_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2458_);
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
v___x_2466_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2464_, v___x_2465_, v___x_2452_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
if (lean_obj_tag(v___x_2466_) == 0)
{
uint8_t v_lift_2467_; 
v_lift_2467_ = lean_ctor_get_uint8(v___y_2456_, 10);
if (v_lift_2467_ == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
v_a_2468_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2470_ = v___x_2466_;
v_isShared_2471_ = v_isSharedCheck_2480_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2466_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2480_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_mk_empty_array_with_capacity(v___x_2472_);
v___x_2474_ = lean_array_push(v___x_2473_, v_x_2455_);
v___x_2475_ = lean_expr_abstract(v_a_2468_, v___x_2474_);
lean_dec_ref(v___x_2474_);
lean_dec(v_a_2468_);
v___x_2476_ = lean_apply_2(v_mk_2453_, v_a_2454_, v___x_2475_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2476_);
v___x_2478_ = v___x_2470_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_a_2481_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2481_);
lean_dec_ref(v___x_2466_);
v___x_2482_ = l_Lean_Expr_fvarId_x21(v_x_2455_);
v___x_2483_ = l_Lean_Meta_ExtractLets_flushDecls(v___x_2482_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2497_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2497_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2497_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2488_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_2484_, v_a_2481_);
lean_dec(v_a_2484_);
v___x_2489_ = lean_unsigned_to_nat(1u);
v___x_2490_ = lean_mk_empty_array_with_capacity(v___x_2489_);
v___x_2491_ = lean_array_push(v___x_2490_, v_x_2455_);
v___x_2492_ = lean_expr_abstract(v___x_2488_, v___x_2491_);
lean_dec_ref(v___x_2491_);
lean_dec_ref(v___x_2488_);
v___x_2493_ = lean_apply_2(v_mk_2453_, v_a_2454_, v___x_2492_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2493_);
v___x_2495_ = v___x_2486_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_a_2481_);
lean_dec_ref(v_x_2455_);
lean_dec_ref(v_a_2454_);
lean_dec_ref(v_mk_2453_);
v_a_2498_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2483_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2483_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
else
{
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v_x_2455_);
lean_dec_ref(v_a_2454_);
lean_dec_ref(v_mk_2453_);
return v___x_2466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(lean_object* v_fvars_2506_, lean_object* v_b_2507_, lean_object* v___x_2508_, lean_object* v_mk_2509_, lean_object* v_a_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
uint8_t v___x_53178__boxed_2520_; lean_object* v_res_2521_; 
v___x_53178__boxed_2520_ = lean_unbox(v___x_2508_);
v_res_2521_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_2506_, v_b_2507_, v___x_53178__boxed_2520_, v_mk_2509_, v_a_2510_, v_x_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec_ref(v_b_2507_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(lean_object* v_fvars_2522_, lean_object* v_n_2523_, lean_object* v_t_2524_, lean_object* v_b_2525_, uint8_t v_i_2526_, lean_object* v_mk_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
uint8_t v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = 0;
lean_inc(v_a_2534_);
lean_inc_ref(v_a_2533_);
lean_inc(v_a_2532_);
lean_inc_ref(v_a_2531_);
lean_inc(v_a_2530_);
lean_inc(v_a_2529_);
lean_inc_ref(v_a_2528_);
lean_inc(v_fvars_2522_);
v___x_2537_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2522_, v_t_2524_, v___x_2536_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2537_) == 0)
{
uint8_t v_underBinder_2538_; 
v_underBinder_2538_ = lean_ctor_get_uint8(v_a_2528_, 4);
if (v_underBinder_2538_ == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_n_2523_);
lean_dec(v_fvars_2522_);
v_a_2539_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2541_ = v___x_2537_;
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2537_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_apply_2(v_mk_2527_, v_a_2539_, v_b_2525_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; 
v_a_2548_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2537_);
v___x_2549_ = lean_box(v___x_2536_);
lean_inc(v_a_2548_);
v___f_2550_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed), 14, 5);
lean_closure_set(v___f_2550_, 0, v_fvars_2522_);
lean_closure_set(v___f_2550_, 1, v_b_2525_);
lean_closure_set(v___f_2550_, 2, v___x_2549_);
lean_closure_set(v___f_2550_, 3, v_mk_2527_);
lean_closure_set(v___f_2550_, 4, v_a_2548_);
v___x_2551_ = 0;
v___x_2552_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_2523_, v_i_2526_, v_a_2548_, v___f_2550_, v___x_2551_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
return v___x_2552_;
}
}
else
{
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec_ref(v_mk_2527_);
lean_dec_ref(v_b_2525_);
lean_dec(v_n_2523_);
lean_dec(v_fvars_2522_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(lean_object* v_fvars_2553_, lean_object* v_n_2554_, lean_object* v_t_2555_, lean_object* v_b_2556_, lean_object* v_i_2557_, lean_object* v_mk_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
uint8_t v_i_boxed_2567_; lean_object* v_res_2568_; 
v_i_boxed_2567_ = lean_unbox(v_i_2557_);
v_res_2568_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(v_fvars_2553_, v_n_2554_, v_t_2555_, v_b_2556_, v_i_boxed_2567_, v_mk_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___boxed(lean_object* v_fvars_2569_, lean_object* v_e_2570_, lean_object* v_topLevel_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
uint8_t v_topLevel_boxed_2580_; lean_object* v_res_2581_; 
v_topLevel_boxed_2580_ = lean_unbox(v_topLevel_2571_);
v_res_2581_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2569_, v_e_2570_, v_topLevel_boxed_2580_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
return v_res_2581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2));
v___x_2586_ = lean_unsigned_to_nat(27u);
v___x_2587_ = lean_unsigned_to_nat(1940u);
v___x_2588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1));
v___x_2589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0));
v___x_2590_ = l_mkPanicMessageWithDecl(v___x_2589_, v___x_2588_, v___x_2587_, v___x_2586_, v___x_2585_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(uint8_t v_fst_2591_, lean_object* v_fvars_2592_, lean_object* v_b_2593_, uint8_t v___x_2594_, lean_object* v_e_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, uint8_t v_isLet_2598_, uint8_t v_topLevel_2599_, lean_object* v_x_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
if (v_fst_2591_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_inc_ref(v_x_2600_);
v___x_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_x_2600_);
lean_ctor_set(v___x_2609_, 1, v_fvars_2592_);
v___x_2610_ = lean_expr_instantiate1(v_b_2593_, v_x_2600_);
v___x_2611_ = l_Lean_Meta_ExtractLets_extractCore(v___x_2609_, v___x_2610_, v___x_2594_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2611_) == 0)
{
if (lean_obj_tag(v_e_2595_) == 8)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2647_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2647_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2647_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v_declName_2616_; lean_object* v_type_2617_; lean_object* v_value_2618_; lean_object* v_body_2619_; uint8_t v_nondep_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___y_2626_; size_t v___x_2641_; size_t v___x_2642_; uint8_t v___x_2643_; 
v_declName_2616_ = lean_ctor_get(v_e_2595_, 0);
v_type_2617_ = lean_ctor_get(v_e_2595_, 1);
v_value_2618_ = lean_ctor_get(v_e_2595_, 2);
v_body_2619_ = lean_ctor_get(v_e_2595_, 3);
v_nondep_2620_ = lean_ctor_get_uint8(v_e_2595_, sizeof(void*)*4 + 8);
v___x_2621_ = lean_unsigned_to_nat(1u);
v___x_2622_ = lean_mk_empty_array_with_capacity(v___x_2621_);
v___x_2623_ = lean_array_push(v___x_2622_, v_x_2600_);
v___x_2624_ = lean_expr_abstract(v_a_2612_, v___x_2623_);
lean_dec_ref(v___x_2623_);
lean_dec(v_a_2612_);
v___x_2641_ = lean_ptr_addr(v_type_2617_);
v___x_2642_ = lean_ptr_addr(v_a_2596_);
v___x_2643_ = lean_usize_dec_eq(v___x_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
v___y_2626_ = v___x_2643_;
goto v___jp_2625_;
}
else
{
size_t v___x_2644_; size_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2644_ = lean_ptr_addr(v_value_2618_);
v___x_2645_ = lean_ptr_addr(v_a_2597_);
v___x_2646_ = lean_usize_dec_eq(v___x_2644_, v___x_2645_);
v___y_2626_ = v___x_2646_;
goto v___jp_2625_;
}
v___jp_2625_:
{
if (v___y_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
lean_inc(v_declName_2616_);
lean_dec_ref(v_e_2595_);
v___x_2627_ = l_Lean_Expr_letE___override(v_declName_2616_, v_a_2596_, v_a_2597_, v___x_2624_, v_nondep_2620_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2627_);
v___x_2629_ = v___x_2614_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
else
{
size_t v___x_2631_; size_t v___x_2632_; uint8_t v___x_2633_; 
v___x_2631_ = lean_ptr_addr(v_body_2619_);
v___x_2632_ = lean_ptr_addr(v___x_2624_);
v___x_2633_ = lean_usize_dec_eq(v___x_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
lean_inc(v_declName_2616_);
lean_dec_ref(v_e_2595_);
v___x_2634_ = l_Lean_Expr_letE___override(v_declName_2616_, v_a_2596_, v_a_2597_, v___x_2624_, v_nondep_2620_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2634_);
v___x_2636_ = v___x_2614_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v___x_2639_; 
lean_dec_ref(v___x_2624_);
lean_dec_ref(v_a_2597_);
lean_dec_ref(v_a_2596_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v_e_2595_);
v___x_2639_ = v___x_2614_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_e_2595_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
else
{
lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v_x_2600_);
lean_dec_ref(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec_ref(v_e_2595_);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v___x_2611_, 0);
lean_dec(v_unused_2657_);
v___x_2649_ = v___x_2611_;
v_isShared_2650_ = v_isSharedCheck_2656_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v___x_2611_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2656_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2652_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2651_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2652_);
v___x_2654_ = v___x_2649_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_dec_ref(v_x_2600_);
lean_dec_ref(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec_ref(v_e_2595_);
return v___x_2611_;
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec_ref(v_e_2595_);
v___x_2658_ = l_Lean_Expr_fvarId_x21(v_x_2600_);
lean_inc_ref(v___y_2604_);
v___x_2659_ = l_Lean_FVarId_getDecl___redArg(v___x_2658_, v___y_2604_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
v___x_2661_ = l_Lean_Meta_ExtractLets_addDecl___redArg(v_a_2660_, v_isLet_2598_, v___y_2601_, v___y_2603_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec_ref(v___x_2661_);
v___x_2662_ = lean_expr_instantiate1(v_b_2593_, v_x_2600_);
lean_dec_ref(v_x_2600_);
v___x_2663_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2592_, v___x_2662_, v_topLevel_2599_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2663_;
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_x_2600_);
lean_dec(v_fvars_2592_);
v_a_2664_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2661_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2661_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
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
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_x_2600_);
lean_dec(v_fvars_2592_);
v_a_2672_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2659_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2659_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(lean_object** _args){
lean_object* v_fst_2680_ = _args[0];
lean_object* v_fvars_2681_ = _args[1];
lean_object* v_b_2682_ = _args[2];
lean_object* v___x_2683_ = _args[3];
lean_object* v_e_2684_ = _args[4];
lean_object* v_a_2685_ = _args[5];
lean_object* v_a_2686_ = _args[6];
lean_object* v_isLet_2687_ = _args[7];
lean_object* v_topLevel_2688_ = _args[8];
lean_object* v_x_2689_ = _args[9];
lean_object* v___y_2690_ = _args[10];
lean_object* v___y_2691_ = _args[11];
lean_object* v___y_2692_ = _args[12];
lean_object* v___y_2693_ = _args[13];
lean_object* v___y_2694_ = _args[14];
lean_object* v___y_2695_ = _args[15];
lean_object* v___y_2696_ = _args[16];
lean_object* v___y_2697_ = _args[17];
_start:
{
uint8_t v_fst_53330__boxed_2698_; uint8_t v___x_53331__boxed_2699_; uint8_t v_isLet_boxed_2700_; uint8_t v_topLevel_boxed_2701_; lean_object* v_res_2702_; 
v_fst_53330__boxed_2698_ = lean_unbox(v_fst_2680_);
v___x_53331__boxed_2699_ = lean_unbox(v___x_2683_);
v_isLet_boxed_2700_ = lean_unbox(v_isLet_2687_);
v_topLevel_boxed_2701_ = lean_unbox(v_topLevel_2688_);
v_res_2702_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_53330__boxed_2698_, v_fvars_2681_, v_b_2682_, v___x_53331__boxed_2699_, v_e_2684_, v_a_2685_, v_a_2686_, v_isLet_boxed_2700_, v_topLevel_boxed_2701_, v_x_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec_ref(v_b_2682_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(lean_object* v_fvars_2703_, lean_object* v_e_2704_, uint8_t v_isLet_2705_, lean_object* v_n_2706_, lean_object* v_t_2707_, lean_object* v_v_2708_, lean_object* v_b_2709_, uint8_t v_topLevel_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; uint8_t v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = 0;
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
lean_inc(v_a_2715_);
lean_inc_ref(v_a_2714_);
lean_inc(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_fvars_2703_);
v___x_2734_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2703_, v_t_2707_, v___x_2733_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2853_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2853_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2853_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; 
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
lean_inc(v_a_2715_);
lean_inc_ref(v_a_2714_);
lean_inc(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_fvars_2703_);
v___x_2739_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2703_, v_v_2708_, v___x_2733_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2852_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2852_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2852_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v___y_2747_; uint8_t v___y_2748_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; uint8_t v_descend_2792_; uint8_t v_underBinder_2793_; uint8_t v_usedOnly_2794_; uint8_t v_merge_2795_; uint8_t v_lift_2796_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; uint8_t v___y_2834_; 
v_descend_2792_ = lean_ctor_get_uint8(v_a_2711_, 3);
v_underBinder_2793_ = lean_ctor_get_uint8(v_a_2711_, 4);
v_usedOnly_2794_ = lean_ctor_get_uint8(v_a_2711_, 5);
v_merge_2795_ = lean_ctor_get_uint8(v_a_2711_, 6);
v_lift_2796_ = lean_ctor_get_uint8(v_a_2711_, 10);
if (v_usedOnly_2794_ == 0)
{
v___y_2834_ = v___x_2733_;
goto v___jp_2833_;
}
else
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Lean_Expr_hasLooseBVars(v_b_2709_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_del_object(v___x_2742_);
lean_dec(v_a_2740_);
lean_del_object(v___x_2737_);
lean_dec(v_a_2735_);
lean_dec(v_n_2706_);
lean_dec_ref(v_e_2704_);
v___x_2851_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2703_, v_b_2709_, v_topLevel_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2851_;
}
else
{
v___y_2834_ = v___x_2733_;
goto v___jp_2833_;
}
}
v___jp_2744_:
{
if (v___y_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_dec_ref(v___y_2745_);
lean_dec_ref(v_e_2704_);
v___x_2749_ = l_Lean_Expr_letE___override(v___y_2747_, v_a_2735_, v_a_2740_, v_b_2709_, v___y_2746_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2749_);
v___x_2751_ = v___x_2742_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
size_t v___x_2753_; size_t v___x_2754_; uint8_t v___x_2755_; 
v___x_2753_ = lean_ptr_addr(v___y_2745_);
lean_dec_ref(v___y_2745_);
v___x_2754_ = lean_ptr_addr(v_b_2709_);
v___x_2755_ = lean_usize_dec_eq(v___x_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
lean_dec_ref(v_e_2704_);
v___x_2756_ = l_Lean_Expr_letE___override(v___y_2747_, v_a_2735_, v_a_2740_, v_b_2709_, v___y_2746_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2756_);
v___x_2758_ = v___x_2742_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
else
{
lean_object* v___x_2761_; 
lean_dec(v___y_2747_);
lean_dec(v_a_2740_);
lean_dec(v_a_2735_);
lean_dec_ref(v_b_2709_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v_e_2704_);
v___x_2761_ = v___x_2742_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_e_2704_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
v___jp_2763_:
{
if (lean_obj_tag(v_e_2704_) == 8)
{
lean_object* v_declName_2764_; lean_object* v_type_2765_; lean_object* v_value_2766_; lean_object* v_body_2767_; uint8_t v_nondep_2768_; size_t v___x_2769_; size_t v___x_2770_; uint8_t v___x_2771_; 
lean_del_object(v___x_2737_);
v_declName_2764_ = lean_ctor_get(v_e_2704_, 0);
v_type_2765_ = lean_ctor_get(v_e_2704_, 1);
v_value_2766_ = lean_ctor_get(v_e_2704_, 2);
v_body_2767_ = lean_ctor_get(v_e_2704_, 3);
v_nondep_2768_ = lean_ctor_get_uint8(v_e_2704_, sizeof(void*)*4 + 8);
v___x_2769_ = lean_ptr_addr(v_type_2765_);
v___x_2770_ = lean_ptr_addr(v_a_2735_);
v___x_2771_ = lean_usize_dec_eq(v___x_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_inc(v_declName_2764_);
lean_inc_ref(v_body_2767_);
v___y_2745_ = v_body_2767_;
v___y_2746_ = v_nondep_2768_;
v___y_2747_ = v_declName_2764_;
v___y_2748_ = v___x_2771_;
goto v___jp_2744_;
}
else
{
size_t v___x_2772_; size_t v___x_2773_; uint8_t v___x_2774_; 
v___x_2772_ = lean_ptr_addr(v_value_2766_);
v___x_2773_ = lean_ptr_addr(v_a_2740_);
v___x_2774_ = lean_usize_dec_eq(v___x_2772_, v___x_2773_);
lean_inc(v_declName_2764_);
lean_inc_ref(v_body_2767_);
v___y_2745_ = v_body_2767_;
v___y_2746_ = v_nondep_2768_;
v___y_2747_ = v_declName_2764_;
v___y_2748_ = v___x_2774_;
goto v___jp_2744_;
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
lean_del_object(v___x_2742_);
lean_dec(v_a_2740_);
lean_dec(v_a_2735_);
lean_dec_ref(v_b_2709_);
lean_dec_ref(v_e_2704_);
v___x_2775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
v___x_2776_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_2775_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2776_);
v___x_2778_ = v___x_2737_;
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
}
v___jp_2780_:
{
uint8_t v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = 0;
v___x_2791_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_2789_, v_a_2735_, v_a_2740_, v___y_2786_, v___x_2733_, v___x_2790_, v___y_2785_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2787_, v___y_2788_);
return v___x_2791_;
}
v___jp_2797_:
{
if (v_underBinder_2793_ == 0)
{
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
goto v___jp_2763_;
}
else
{
if (v_descend_2792_ == 0)
{
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
goto v___jp_2763_;
}
else
{
lean_del_object(v___x_2742_);
lean_del_object(v___x_2737_);
lean_dec_ref(v_b_2709_);
lean_dec_ref(v_e_2704_);
v___y_2781_ = v___y_2798_;
v___y_2782_ = v___y_2799_;
v___y_2783_ = v___y_2800_;
v___y_2784_ = v___y_2801_;
v___y_2785_ = v___y_2803_;
v___y_2786_ = v___y_2802_;
v___y_2787_ = v___y_2804_;
v___y_2788_ = v___y_2806_;
v___y_2789_ = v___y_2805_;
goto v___jp_2780_;
}
}
}
v___jp_2807_:
{
lean_object* v___x_2816_; 
lean_inc(v___y_2815_);
lean_inc_ref(v___y_2814_);
lean_inc(v_a_2740_);
lean_inc(v_a_2735_);
v___x_2816_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(v_fvars_2703_, v_n_2706_, v_a_2735_, v_a_2740_, v___y_2809_, v___y_2811_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v_fst_2818_; lean_object* v_snd_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___f_2823_; uint8_t v___x_2824_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
v_fst_2818_ = lean_ctor_get(v_a_2817_, 0);
lean_inc(v_fst_2818_);
v_snd_2819_ = lean_ctor_get(v_a_2817_, 1);
lean_inc(v_snd_2819_);
lean_dec(v_a_2817_);
v___x_2820_ = lean_box(v___x_2733_);
v___x_2821_ = lean_box(v_isLet_2705_);
v___x_2822_ = lean_box(v_topLevel_2710_);
lean_inc(v_a_2740_);
lean_inc(v_a_2735_);
lean_inc_ref(v_e_2704_);
lean_inc_ref(v_b_2709_);
lean_inc(v_fst_2818_);
v___f_2823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed), 18, 9);
lean_closure_set(v___f_2823_, 0, v_fst_2818_);
lean_closure_set(v___f_2823_, 1, v_fvars_2703_);
lean_closure_set(v___f_2823_, 2, v_b_2709_);
lean_closure_set(v___f_2823_, 3, v___x_2820_);
lean_closure_set(v___f_2823_, 4, v_e_2704_);
lean_closure_set(v___f_2823_, 5, v_a_2735_);
lean_closure_set(v___f_2823_, 6, v_a_2740_);
lean_closure_set(v___f_2823_, 7, v___x_2821_);
lean_closure_set(v___f_2823_, 8, v___x_2822_);
v___x_2824_ = lean_unbox(v_fst_2818_);
lean_dec(v_fst_2818_);
if (v___x_2824_ == 0)
{
v___y_2798_ = v___y_2810_;
v___y_2799_ = v___y_2811_;
v___y_2800_ = v___y_2812_;
v___y_2801_ = v___y_2813_;
v___y_2802_ = v___f_2823_;
v___y_2803_ = v___y_2809_;
v___y_2804_ = v___y_2814_;
v___y_2805_ = v_snd_2819_;
v___y_2806_ = v___y_2815_;
goto v___jp_2797_;
}
else
{
if (v___y_2808_ == 0)
{
lean_del_object(v___x_2742_);
lean_del_object(v___x_2737_);
lean_dec_ref(v_b_2709_);
lean_dec_ref(v_e_2704_);
v___y_2781_ = v___y_2810_;
v___y_2782_ = v___y_2811_;
v___y_2783_ = v___y_2812_;
v___y_2784_ = v___y_2813_;
v___y_2785_ = v___y_2809_;
v___y_2786_ = v___f_2823_;
v___y_2787_ = v___y_2814_;
v___y_2788_ = v___y_2815_;
v___y_2789_ = v_snd_2819_;
goto v___jp_2780_;
}
else
{
v___y_2798_ = v___y_2810_;
v___y_2799_ = v___y_2811_;
v___y_2800_ = v___y_2812_;
v___y_2801_ = v___y_2813_;
v___y_2802_ = v___f_2823_;
v___y_2803_ = v___y_2809_;
v___y_2804_ = v___y_2814_;
v___y_2805_ = v_snd_2819_;
v___y_2806_ = v___y_2815_;
goto v___jp_2797_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_del_object(v___x_2742_);
lean_dec(v_a_2740_);
lean_del_object(v___x_2737_);
lean_dec(v_a_2735_);
lean_dec_ref(v_b_2709_);
lean_dec_ref(v_e_2704_);
lean_dec(v_fvars_2703_);
v_a_2825_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2816_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2816_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
v___jp_2833_:
{
if (v_merge_2795_ == 0)
{
v___y_2808_ = v___y_2834_;
v___y_2809_ = v_a_2711_;
v___y_2810_ = v_a_2712_;
v___y_2811_ = v_a_2713_;
v___y_2812_ = v_a_2714_;
v___y_2813_ = v_a_2715_;
v___y_2814_ = v_a_2716_;
v___y_2815_ = v_a_2717_;
goto v___jp_2807_;
}
else
{
lean_object* v___x_2835_; lean_object* v_valueMap_2836_; lean_object* v___x_2837_; 
v___x_2835_ = lean_st_ref_get(v_a_2713_);
v_valueMap_2836_ = lean_ctor_get(v___x_2835_, 2);
lean_inc_ref(v_valueMap_2836_);
lean_dec(v___x_2835_);
v___x_2837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_2836_, v_a_2740_);
lean_dec_ref(v_valueMap_2836_);
if (lean_obj_tag(v___x_2837_) == 1)
{
lean_del_object(v___x_2742_);
lean_dec(v_a_2740_);
lean_del_object(v___x_2737_);
lean_dec(v_a_2735_);
lean_dec(v_n_2706_);
lean_dec_ref(v_e_2704_);
if (v_isLet_2705_ == 0)
{
lean_object* v_val_2838_; 
v_val_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_val_2838_);
lean_dec_ref(v___x_2837_);
v___y_2720_ = v_val_2838_;
v___y_2721_ = v_a_2711_;
v___y_2722_ = v_a_2712_;
v___y_2723_ = v_a_2713_;
v___y_2724_ = v_a_2714_;
v___y_2725_ = v_a_2715_;
v___y_2726_ = v_a_2716_;
v___y_2727_ = v_a_2717_;
goto v___jp_2719_;
}
else
{
if (v_lift_2796_ == 0)
{
lean_object* v_val_2839_; 
v_val_2839_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_val_2839_);
lean_dec_ref(v___x_2837_);
v___y_2720_ = v_val_2839_;
v___y_2721_ = v_a_2711_;
v___y_2722_ = v_a_2712_;
v___y_2723_ = v_a_2713_;
v___y_2724_ = v_a_2714_;
v___y_2725_ = v_a_2715_;
v___y_2726_ = v_a_2716_;
v___y_2727_ = v_a_2717_;
goto v___jp_2719_;
}
else
{
lean_object* v_val_2840_; lean_object* v___x_2841_; 
v_val_2840_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_val_2840_);
lean_dec_ref(v___x_2837_);
v___x_2841_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_val_2840_, v_a_2713_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_dec_ref(v___x_2841_);
v___y_2720_ = v_val_2840_;
v___y_2721_ = v_a_2711_;
v___y_2722_ = v_a_2712_;
v___y_2723_ = v_a_2713_;
v___y_2724_ = v_a_2714_;
v___y_2725_ = v_a_2715_;
v___y_2726_ = v_a_2716_;
v___y_2727_ = v_a_2717_;
goto v___jp_2719_;
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_val_2840_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec_ref(v_b_2709_);
lean_dec(v_fvars_2703_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
else
{
lean_dec(v___x_2837_);
v___y_2808_ = v___y_2834_;
v___y_2809_ = v_a_2711_;
v___y_2810_ = v_a_2712_;
v___y_2811_ = v_a_2713_;
v___y_2812_ = v_a_2714_;
v___y_2813_ = v_a_2715_;
v___y_2814_ = v_a_2716_;
v___y_2815_ = v_a_2717_;
goto v___jp_2807_;
}
}
}
}
}
else
{
lean_del_object(v___x_2737_);
lean_dec(v_a_2735_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec_ref(v_b_2709_);
lean_dec(v_n_2706_);
lean_dec_ref(v_e_2704_);
lean_dec(v_fvars_2703_);
return v___x_2739_;
}
}
}
else
{
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec_ref(v_b_2709_);
lean_dec_ref(v_v_2708_);
lean_dec(v_n_2706_);
lean_dec_ref(v_e_2704_);
lean_dec(v_fvars_2703_);
return v___x_2734_;
}
v___jp_2719_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_inc(v___y_2720_);
v___x_2728_ = l_Lean_Expr_fvar___override(v___y_2720_);
v___x_2729_ = lean_expr_instantiate1(v_b_2709_, v___x_2728_);
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_b_2709_);
v___x_2730_ = lean_box(v_topLevel_2710_);
v___x_2731_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___boxed), 11, 3);
lean_closure_set(v___x_2731_, 0, v_fvars_2703_);
lean_closure_set(v___x_2731_, 1, v___x_2729_);
lean_closure_set(v___x_2731_, 2, v___x_2730_);
v___x_2732_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(v___y_2720_, v___x_2731_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(lean_object* v_fvars_2854_, lean_object* v_struct_2855_, lean_object* v___y_2856_, lean_object* v_typeName_2857_, lean_object* v_idx_2858_, lean_object* v_e_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
uint8_t v___y_53092__boxed_2868_; lean_object* v_res_2869_; 
v___y_53092__boxed_2868_ = lean_unbox(v___y_2856_);
v_res_2869_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(v_fvars_2854_, v_struct_2855_, v___y_53092__boxed_2868_, v_typeName_2857_, v_idx_2858_, v_e_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v_res_2869_;
}
}
static lean_object* _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2873_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3));
v___x_2874_ = lean_unsigned_to_nat(75u);
v___x_2875_ = lean_unsigned_to_nat(229u);
v___x_2876_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2));
v___x_2877_ = ((lean_object*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1));
v___x_2878_ = l_mkPanicMessageWithDecl(v___x_2877_, v___x_2876_, v___x_2875_, v___x_2874_, v___x_2873_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3(uint8_t v_descend_2879_, lean_object* v_e_2880_, lean_object* v_fvars_2881_, uint8_t v___x_2882_, uint8_t v_topLevel_2883_, uint8_t v___y_2884_, lean_object* v_____r_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_k_2895_; 
switch(lean_obj_tag(v_e_2880_))
{
case 5:
{
lean_object* v___x_2898_; lean_object* v_dummy_2899_; lean_object* v_nargs_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2898_ = l_Lean_Expr_getAppFn(v_e_2880_);
v_dummy_2899_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0);
v_nargs_2900_ = l_Lean_Expr_getAppNumArgs(v_e_2880_);
lean_inc(v_nargs_2900_);
v___x_2901_ = lean_mk_array(v_nargs_2900_, v_dummy_2899_);
v___x_2902_ = lean_unsigned_to_nat(1u);
v___x_2903_ = lean_nat_sub(v_nargs_2900_, v___x_2902_);
lean_dec(v_nargs_2900_);
lean_inc_ref(v_e_2880_);
v___x_2904_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2880_, v___x_2901_, v___x_2903_);
v___x_2905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed), 11, 3);
lean_closure_set(v___x_2905_, 0, v_fvars_2881_);
lean_closure_set(v___x_2905_, 1, v___x_2898_);
lean_closure_set(v___x_2905_, 2, v___x_2904_);
v_k_2895_ = v___x_2905_;
goto v___jp_2894_;
}
case 6:
{
lean_object* v_binderName_2906_; lean_object* v_binderType_2907_; lean_object* v_body_2908_; uint8_t v_binderInfo_2909_; lean_object* v___x_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_binderName_2906_ = lean_ctor_get(v_e_2880_, 0);
v_binderType_2907_ = lean_ctor_get(v_e_2880_, 1);
v_body_2908_ = lean_ctor_get(v_e_2880_, 2);
v_binderInfo_2909_ = lean_ctor_get_uint8(v_e_2880_, sizeof(void*)*3 + 8);
v___x_2910_ = lean_box(v_binderInfo_2909_);
lean_inc_ref(v_body_2908_);
lean_inc_ref(v_binderType_2907_);
lean_inc_ref(v_e_2880_);
lean_inc(v_binderName_2906_);
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2911_, 0, v_binderName_2906_);
lean_closure_set(v___f_2911_, 1, v___x_2910_);
lean_closure_set(v___f_2911_, 2, v_e_2880_);
lean_closure_set(v___f_2911_, 3, v_binderType_2907_);
lean_closure_set(v___f_2911_, 4, v_body_2908_);
v___x_2912_ = lean_box(v_binderInfo_2909_);
lean_inc_ref(v_body_2908_);
lean_inc_ref(v_binderType_2907_);
lean_inc(v_binderName_2906_);
v___x_2913_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2913_, 0, v_fvars_2881_);
lean_closure_set(v___x_2913_, 1, v_binderName_2906_);
lean_closure_set(v___x_2913_, 2, v_binderType_2907_);
lean_closure_set(v___x_2913_, 3, v_body_2908_);
lean_closure_set(v___x_2913_, 4, v___x_2912_);
lean_closure_set(v___x_2913_, 5, v___f_2911_);
v_k_2895_ = v___x_2913_;
goto v___jp_2894_;
}
case 7:
{
lean_object* v_binderName_2914_; lean_object* v_binderType_2915_; lean_object* v_body_2916_; uint8_t v_binderInfo_2917_; lean_object* v___x_2918_; lean_object* v___f_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_binderName_2914_ = lean_ctor_get(v_e_2880_, 0);
v_binderType_2915_ = lean_ctor_get(v_e_2880_, 1);
v_body_2916_ = lean_ctor_get(v_e_2880_, 2);
v_binderInfo_2917_ = lean_ctor_get_uint8(v_e_2880_, sizeof(void*)*3 + 8);
v___x_2918_ = lean_box(v_binderInfo_2917_);
lean_inc_ref(v_body_2916_);
lean_inc_ref(v_binderType_2915_);
lean_inc_ref(v_e_2880_);
lean_inc(v_binderName_2914_);
v___f_2919_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2919_, 0, v_binderName_2914_);
lean_closure_set(v___f_2919_, 1, v___x_2918_);
lean_closure_set(v___f_2919_, 2, v_e_2880_);
lean_closure_set(v___f_2919_, 3, v_binderType_2915_);
lean_closure_set(v___f_2919_, 4, v_body_2916_);
v___x_2920_ = lean_box(v_binderInfo_2917_);
lean_inc_ref(v_body_2916_);
lean_inc_ref(v_binderType_2915_);
lean_inc(v_binderName_2914_);
v___x_2921_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed), 14, 6);
lean_closure_set(v___x_2921_, 0, v_fvars_2881_);
lean_closure_set(v___x_2921_, 1, v_binderName_2914_);
lean_closure_set(v___x_2921_, 2, v_binderType_2915_);
lean_closure_set(v___x_2921_, 3, v_body_2916_);
lean_closure_set(v___x_2921_, 4, v___x_2920_);
lean_closure_set(v___x_2921_, 5, v___f_2919_);
v_k_2895_ = v___x_2921_;
goto v___jp_2894_;
}
case 8:
{
uint8_t v_nondep_2922_; 
v_nondep_2922_ = lean_ctor_get_uint8(v_e_2880_, sizeof(void*)*4 + 8);
if (v_nondep_2922_ == 0)
{
lean_object* v_declName_2923_; lean_object* v_type_2924_; lean_object* v_value_2925_; lean_object* v_body_2926_; lean_object* v___x_2927_; 
v_declName_2923_ = lean_ctor_get(v_e_2880_, 0);
lean_inc(v_declName_2923_);
v_type_2924_ = lean_ctor_get(v_e_2880_, 1);
lean_inc_ref(v_type_2924_);
v_value_2925_ = lean_ctor_get(v_e_2880_, 2);
lean_inc_ref(v_value_2925_);
v_body_2926_ = lean_ctor_get(v_e_2880_, 3);
lean_inc_ref(v_body_2926_);
v___x_2927_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2881_, v_e_2880_, v___x_2882_, v_declName_2923_, v_type_2924_, v_value_2925_, v_body_2926_, v_topLevel_2883_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
return v___x_2927_;
}
else
{
lean_object* v_declName_2928_; lean_object* v_type_2929_; lean_object* v_value_2930_; lean_object* v_body_2931_; lean_object* v___x_2932_; 
v_declName_2928_ = lean_ctor_get(v_e_2880_, 0);
lean_inc(v_declName_2928_);
v_type_2929_ = lean_ctor_get(v_e_2880_, 1);
lean_inc_ref(v_type_2929_);
v_value_2930_ = lean_ctor_get(v_e_2880_, 2);
lean_inc_ref(v_value_2930_);
v_body_2931_ = lean_ctor_get(v_e_2880_, 3);
lean_inc_ref(v_body_2931_);
v___x_2932_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_2881_, v_e_2880_, v___y_2884_, v_declName_2928_, v_type_2929_, v_value_2930_, v_body_2931_, v_topLevel_2883_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
return v___x_2932_;
}
}
case 10:
{
lean_object* v_data_2933_; lean_object* v_expr_2934_; lean_object* v___x_2935_; 
v_data_2933_ = lean_ctor_get(v_e_2880_, 0);
v_expr_2934_ = lean_ctor_get(v_e_2880_, 1);
lean_inc_ref(v_expr_2934_);
v___x_2935_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_2881_, v_expr_2934_, v_topLevel_2883_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2950_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2950_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2950_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
size_t v___x_2940_; size_t v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = lean_ptr_addr(v_expr_2934_);
v___x_2941_ = lean_ptr_addr(v_a_2936_);
v___x_2942_ = lean_usize_dec_eq(v___x_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
lean_inc(v_data_2933_);
lean_dec_ref(v_e_2880_);
v___x_2943_ = l_Lean_Expr_mdata___override(v_data_2933_, v_a_2936_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2943_);
v___x_2945_ = v___x_2938_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
else
{
lean_object* v___x_2948_; 
lean_dec(v_a_2936_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v_e_2880_);
v___x_2948_ = v___x_2938_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_e_2880_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_dec_ref(v_e_2880_);
return v___x_2935_;
}
}
case 11:
{
lean_object* v_typeName_2951_; lean_object* v_idx_2952_; lean_object* v_struct_2953_; lean_object* v___x_2954_; lean_object* v___f_2955_; 
v_typeName_2951_ = lean_ctor_get(v_e_2880_, 0);
v_idx_2952_ = lean_ctor_get(v_e_2880_, 1);
v_struct_2953_ = lean_ctor_get(v_e_2880_, 2);
v___x_2954_ = lean_box(v___y_2884_);
lean_inc_ref(v_e_2880_);
lean_inc(v_idx_2952_);
lean_inc(v_typeName_2951_);
lean_inc_ref(v_struct_2953_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed), 14, 6);
lean_closure_set(v___f_2955_, 0, v_fvars_2881_);
lean_closure_set(v___f_2955_, 1, v_struct_2953_);
lean_closure_set(v___f_2955_, 2, v___x_2954_);
lean_closure_set(v___f_2955_, 3, v_typeName_2951_);
lean_closure_set(v___f_2955_, 4, v_idx_2952_);
lean_closure_set(v___f_2955_, 5, v_e_2880_);
v_k_2895_ = v___f_2955_;
goto v___jp_2894_;
}
default: 
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec(v_fvars_2881_);
lean_dec_ref(v_e_2880_);
v___x_2956_ = lean_obj_once(&l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4, &l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once, _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4);
v___x_2957_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(v___x_2956_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
return v___x_2957_;
}
}
v___jp_2894_:
{
if (v_descend_2879_ == 0)
{
lean_object* v___x_2896_; 
lean_dec_ref(v_k_2895_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v_e_2880_);
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; 
lean_dec_ref(v_e_2880_);
v___x_2897_ = lean_apply_8(v_k_2895_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, lean_box(0));
return v___x_2897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(lean_object* v_descend_2958_, lean_object* v_e_2959_, lean_object* v_fvars_2960_, lean_object* v___x_2961_, lean_object* v_topLevel_2962_, lean_object* v___y_2963_, lean_object* v_____r_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v_descend_boxed_2973_; uint8_t v___x_53259__boxed_2974_; uint8_t v_topLevel_boxed_2975_; uint8_t v___y_53260__boxed_2976_; lean_object* v_res_2977_; 
v_descend_boxed_2973_ = lean_unbox(v_descend_2958_);
v___x_53259__boxed_2974_ = lean_unbox(v___x_2961_);
v_topLevel_boxed_2975_ = lean_unbox(v_topLevel_2962_);
v___y_53260__boxed_2976_ = lean_unbox(v___y_2963_);
v_res_2977_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(v_descend_boxed_2973_, v_e_2959_, v_fvars_2960_, v___x_53259__boxed_2974_, v_topLevel_boxed_2975_, v___y_53260__boxed_2976_, v_____r_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore(lean_object* v_fvars_2978_, lean_object* v_e_2979_, uint8_t v_topLevel_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___y_2990_; lean_object* v_a_2991_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_3001_; lean_object* v___y_3002_; uint8_t v___x_3005_; 
v___x_3005_ = l_Lean_Expr_isAtomic(v_e_2979_);
if (v___x_3005_ == 0)
{
uint8_t v_proofs_3006_; uint8_t v_types_3007_; uint8_t v_descend_3008_; lean_object* v___y_3010_; lean_object* v___y_3011_; uint8_t v___y_3028_; 
v_proofs_3006_ = lean_ctor_get_uint8(v_a_2981_, 0);
v_types_3007_ = lean_ctor_get_uint8(v_a_2981_, 1);
v_descend_3008_ = lean_ctor_get_uint8(v_a_2981_, 3);
if (v_descend_3008_ == 0)
{
goto v___jp_3051_;
}
else
{
if (v___x_3005_ == 0)
{
v___y_3028_ = v___x_3005_;
goto v___jp_3027_;
}
else
{
goto v___jp_3051_;
}
}
v___jp_3009_:
{
if (v_proofs_3006_ == 0)
{
lean_object* v___x_3012_; 
lean_inc(v_a_2987_);
lean_inc_ref(v_a_2986_);
lean_inc(v_a_2985_);
lean_inc_ref(v_a_2984_);
lean_inc_ref(v_e_2979_);
v___x_3012_ = l_Lean_Meta_isProof(v_e_2979_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; uint8_t v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
v___x_3014_ = lean_unbox(v_a_3013_);
lean_dec(v_a_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
lean_dec_ref(v_e_2979_);
v___x_3015_ = lean_box(0);
lean_inc(v_a_2982_);
v___x_3016_ = lean_apply_9(v___y_3011_, v___x_3015_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, lean_box(0));
v___y_2997_ = v___y_3010_;
v___y_2998_ = v___x_3016_;
goto v___jp_2996_;
}
else
{
lean_dec_ref(v___y_3011_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2981_);
v___y_2990_ = v___y_3010_;
v_a_2991_ = v_e_2979_;
goto v___jp_2989_;
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec_ref(v_e_2979_);
v_a_3017_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3012_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3012_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec_ref(v_e_2979_);
v___x_3025_ = lean_box(0);
lean_inc(v_a_2982_);
v___x_3026_ = lean_apply_9(v___y_3011_, v___x_3025_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, lean_box(0));
v___y_2997_ = v___y_3010_;
v___y_2998_ = v___x_3026_;
goto v___jp_2996_;
}
}
v___jp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3029_ = lean_st_ref_get(v_a_2982_);
v___x_3030_ = lean_box(v_topLevel_2980_);
lean_inc_ref(v_e_2979_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v_e_2979_);
v___x_3032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_3029_, v___x_3031_);
lean_dec(v___x_3029_);
if (lean_obj_tag(v___x_3032_) == 0)
{
uint8_t v___x_3033_; 
v___x_3033_ = l_Lean_Meta_ExtractLets_containsLet(v_e_2979_);
if (v___x_3033_ == 0)
{
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2981_);
lean_dec(v_fvars_2978_);
v___y_2990_ = v___x_3031_;
v_a_2991_ = v_e_2979_;
goto v___jp_2989_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___f_3038_; lean_object* v___x_3039_; lean_object* v___f_3040_; 
v___x_3034_ = lean_box(v_descend_3008_);
v___x_3035_ = lean_box(v___x_3033_);
v___x_3036_ = lean_box(v_topLevel_2980_);
v___x_3037_ = lean_box(v___y_3028_);
lean_inc_ref(v_e_2979_);
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed), 15, 6);
lean_closure_set(v___f_3038_, 0, v___x_3034_);
lean_closure_set(v___f_3038_, 1, v_e_2979_);
lean_closure_set(v___f_3038_, 2, v_fvars_2978_);
lean_closure_set(v___f_3038_, 3, v___x_3035_);
lean_closure_set(v___f_3038_, 4, v___x_3036_);
lean_closure_set(v___f_3038_, 5, v___x_3037_);
v___x_3039_ = lean_box(v_types_3007_);
lean_inc_ref(v___f_3038_);
lean_inc_ref(v_e_2979_);
v___f_3040_ = lean_alloc_closure((void*)(l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed), 12, 3);
lean_closure_set(v___f_3040_, 0, v___x_3039_);
lean_closure_set(v___f_3040_, 1, v_e_2979_);
lean_closure_set(v___f_3040_, 2, v___f_3038_);
if (v_topLevel_2980_ == 0)
{
lean_dec_ref(v___f_3038_);
v___y_3010_ = v___x_3031_;
v___y_3011_ = v___f_3040_;
goto v___jp_3009_;
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_Expr_isLet(v_e_2979_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; 
v___x_3042_ = l_Lean_Expr_isMData(v_e_2979_);
if (v___x_3042_ == 0)
{
lean_dec_ref(v___f_3038_);
v___y_3010_ = v___x_3031_;
v___y_3011_ = v___f_3040_;
goto v___jp_3009_;
}
else
{
lean_dec_ref(v___f_3040_);
lean_dec_ref(v_e_2979_);
v___y_3001_ = v___x_3031_;
v___y_3002_ = v___f_3038_;
goto v___jp_3000_;
}
}
else
{
lean_dec_ref(v___f_3040_);
lean_dec_ref(v_e_2979_);
v___y_3001_ = v___x_3031_;
v___y_3002_ = v___f_3038_;
goto v___jp_3000_;
}
}
}
}
else
{
lean_object* v_val_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v___x_3031_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec_ref(v_e_2979_);
lean_dec(v_fvars_2978_);
v_val_3043_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3032_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_val_3043_);
lean_dec(v___x_3032_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 0);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_val_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
v___jp_3051_:
{
if (v_topLevel_2980_ == 0)
{
lean_object* v___x_3052_; 
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_fvars_2978_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_e_2979_);
return v___x_3052_;
}
else
{
if (v___x_3005_ == 0)
{
v___y_3028_ = v___x_3005_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3053_; 
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_fvars_2978_);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_e_2979_);
return v___x_3053_;
}
}
}
}
else
{
lean_object* v___x_3054_; 
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_fvars_2978_);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_e_2979_);
return v___x_3054_;
}
v___jp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = lean_st_ref_take(v_a_2982_);
lean_inc_ref(v_a_2991_);
v___x_2993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_2992_, v___y_2990_, v_a_2991_);
v___x_2994_ = lean_st_ref_set(v_a_2982_, v___x_2993_);
lean_dec(v_a_2982_);
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_a_2991_);
return v___x_2995_;
}
v___jp_2996_:
{
if (lean_obj_tag(v___y_2998_) == 0)
{
lean_object* v_a_2999_; 
v_a_2999_ = lean_ctor_get(v___y_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___y_2998_);
v___y_2990_ = v___y_2997_;
v_a_2991_ = v_a_2999_;
goto v___jp_2989_;
}
else
{
lean_dec_ref(v___y_2997_);
lean_dec(v_a_2982_);
return v___y_2998_;
}
}
v___jp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_box(0);
lean_inc(v_a_2982_);
v___x_3004_ = lean_apply_9(v___y_3002_, v___x_3003_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, lean_box(0));
v___y_2997_ = v___y_3001_;
v___y_2998_ = v___x_3004_;
goto v___jp_2996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractCore___lam__2(lean_object* v_fvars_3055_, lean_object* v_struct_3056_, uint8_t v___y_3057_, lean_object* v_typeName_3058_, lean_object* v_idx_3059_, lean_object* v_e_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v___x_3069_; 
lean_inc_ref(v_struct_3056_);
v___x_3069_ = l_Lean_Meta_ExtractLets_extractCore(v_fvars_3055_, v_struct_3056_, v___y_3057_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3084_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3084_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3084_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
size_t v___x_3074_; size_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3074_ = lean_ptr_addr(v_struct_3056_);
lean_dec_ref(v_struct_3056_);
v___x_3075_ = lean_ptr_addr(v_a_3070_);
v___x_3076_ = lean_usize_dec_eq(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
lean_dec_ref(v_e_3060_);
v___x_3077_ = l_Lean_Expr_proj___override(v_typeName_3058_, v_idx_3059_, v_a_3070_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3077_);
v___x_3079_ = v___x_3072_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
else
{
lean_object* v___x_3082_; 
lean_dec(v_a_3070_);
lean_dec(v_idx_3059_);
lean_dec(v_typeName_3058_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v_e_3060_);
v___x_3082_ = v___x_3072_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_e_3060_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_dec_ref(v_e_3060_);
lean_dec(v_idx_3059_);
lean_dec(v_typeName_3058_);
lean_dec_ref(v_struct_3056_);
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(lean_object* v_fvars_3085_, lean_object* v_sz_3086_, lean_object* v_i_3087_, lean_object* v_bs_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
size_t v_sz_boxed_3097_; size_t v_i_boxed_3098_; lean_object* v_res_3099_; 
v_sz_boxed_3097_ = lean_unbox_usize(v_sz_3086_);
lean_dec(v_sz_3086_);
v_i_boxed_3098_ = lean_unbox_usize(v_i_3087_);
lean_dec(v_i_3087_);
v_res_3099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_3085_, v_sz_boxed_3097_, v_i_boxed_3098_, v_bs_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(lean_object* v_upperBound_3100_, lean_object* v_fst_3101_, lean_object* v_fvars_3102_, lean_object* v_a_3103_, lean_object* v_b_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3100_, v_fst_3101_, v_fvars_3102_, v_a_3103_, v_b_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec_ref(v_fst_3101_);
lean_dec(v_upperBound_3100_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(lean_object* v_fvars_3114_, lean_object* v_e_3115_, lean_object* v_isLet_3116_, lean_object* v_n_3117_, lean_object* v_t_3118_, lean_object* v_v_3119_, lean_object* v_b_3120_, lean_object* v_topLevel_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
uint8_t v_isLet_boxed_3130_; uint8_t v_topLevel_boxed_3131_; lean_object* v_res_3132_; 
v_isLet_boxed_3130_ = lean_unbox(v_isLet_3116_);
v_topLevel_boxed_3131_ = lean_unbox(v_topLevel_3121_);
v_res_3132_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_3114_, v_e_3115_, v_isLet_boxed_3130_, v_n_3117_, v_t_3118_, v_v_3119_, v_b_3120_, v_topLevel_boxed_3131_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(lean_object* v_00_u03b1_3133_, lean_object* v_name_3134_, lean_object* v_type_3135_, lean_object* v_val_3136_, lean_object* v_k_3137_, uint8_t v_nondep_3138_, uint8_t v_kind_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_3134_, v_type_3135_, v_val_3136_, v_k_3137_, v_nondep_3138_, v_kind_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(lean_object* v_00_u03b1_3149_, lean_object* v_name_3150_, lean_object* v_type_3151_, lean_object* v_val_3152_, lean_object* v_k_3153_, lean_object* v_nondep_3154_, lean_object* v_kind_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_nondep_boxed_3164_; uint8_t v_kind_boxed_3165_; lean_object* v_res_3166_; 
v_nondep_boxed_3164_ = lean_unbox(v_nondep_3154_);
v_kind_boxed_3165_ = lean_unbox(v_kind_3155_);
v_res_3166_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_3149_, v_name_3150_, v_type_3151_, v_val_3152_, v_k_3153_, v_nondep_boxed_3164_, v_kind_boxed_3165_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(lean_object* v_00_u03b2_3167_, lean_object* v_m_3168_, lean_object* v_a_3169_, lean_object* v_b_3170_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_3168_, v_a_3169_, v_b_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(lean_object* v_00_u03b2_3172_, lean_object* v_m_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_3173_, v_a_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(lean_object* v_00_u03b2_3176_, lean_object* v_m_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_3176_, v_m_3177_, v_a_3178_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v_m_3177_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(lean_object* v_upperBound_3180_, lean_object* v_fst_3181_, lean_object* v_fvars_3182_, lean_object* v_inst_3183_, lean_object* v_R_3184_, lean_object* v_a_3185_, lean_object* v_b_3186_, lean_object* v_c_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_3180_, v_fst_3181_, v_fvars_3182_, v_a_3185_, v_b_3186_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(lean_object* v_upperBound_3197_, lean_object* v_fst_3198_, lean_object* v_fvars_3199_, lean_object* v_inst_3200_, lean_object* v_R_3201_, lean_object* v_a_3202_, lean_object* v_b_3203_, lean_object* v_c_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_3197_, v_fst_3198_, v_fvars_3199_, v_inst_3200_, v_R_3201_, v_a_3202_, v_b_3203_, v_c_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec_ref(v_fst_3198_);
lean_dec(v_upperBound_3197_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(lean_object* v_00_u03b2_3214_, lean_object* v_m_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_3215_, v_a_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(lean_object* v_00_u03b2_3218_, lean_object* v_m_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_3218_, v_m_3219_, v_a_3220_);
lean_dec_ref(v_a_3220_);
lean_dec_ref(v_m_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(lean_object* v_00_u03b2_3222_, lean_object* v_a_3223_, lean_object* v_x_3224_){
_start:
{
uint8_t v___x_3225_; 
v___x_3225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_3223_, v_x_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3226_, lean_object* v_a_3227_, lean_object* v_x_3228_){
_start:
{
uint8_t v_res_3229_; lean_object* v_r_3230_; 
v_res_3229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_3226_, v_a_3227_, v_x_3228_);
lean_dec(v_x_3228_);
lean_dec_ref(v_a_3227_);
v_r_3230_ = lean_box(v_res_3229_);
return v_r_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(lean_object* v_00_u03b2_3231_, lean_object* v_data_3232_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(lean_object* v_00_u03b2_3234_, lean_object* v_a_3235_, lean_object* v_b_3236_, lean_object* v_x_3237_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_3235_, v_b_3236_, v_x_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(lean_object* v_00_u03b2_3239_, lean_object* v_a_3240_, lean_object* v_x_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_3240_, v_x_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3243_, lean_object* v_a_3244_, lean_object* v_x_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_3243_, v_a_3244_, v_x_3245_);
lean_dec(v_x_3245_);
lean_dec_ref(v_a_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(lean_object* v_00_u03b2_3247_, lean_object* v_a_3248_, lean_object* v_x_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_3248_, v_x_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(lean_object* v_00_u03b2_3251_, lean_object* v_a_3252_, lean_object* v_x_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_3251_, v_a_3252_, v_x_3253_);
lean_dec(v_x_3253_);
lean_dec_ref(v_a_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_3255_, lean_object* v_i_3256_, lean_object* v_source_3257_, lean_object* v_target_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_3256_, v_source_3257_, v_target_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3260_, lean_object* v_x_3261_, lean_object* v_x_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_3261_, v_x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel(lean_object* v_e_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v___x_3273_; lean_object* v_a_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
v___x_3273_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v_e_3264_, v_a_3269_);
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref(v___x_3273_);
v___x_3275_ = lean_box(0);
v___x_3276_ = 1;
v___x_3277_ = l_Lean_Meta_ExtractLets_extractCore(v___x_3275_, v_a_3274_, v___x_3276_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extractTopLevel___boxed(lean_object* v_e_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_e_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(size_t v_sz_3288_, size_t v_i_3289_, lean_object* v_bs_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_usize_dec_lt(v_i_3289_, v_sz_3288_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; 
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_bs_3290_);
return v___x_3300_;
}
else
{
lean_object* v_v_3301_; lean_object* v___x_3302_; 
v_v_3301_ = lean_array_uget_borrowed(v_bs_3290_, v_i_3289_);
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3294_);
lean_inc(v___y_3293_);
lean_inc(v___y_3292_);
lean_inc_ref(v___y_3291_);
lean_inc(v_v_3301_);
v___x_3302_ = l_Lean_Meta_ExtractLets_extractTopLevel(v_v_3301_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; lean_object* v_bs_x27_3305_; size_t v___x_3306_; size_t v___x_3307_; lean_object* v___x_3308_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = lean_unsigned_to_nat(0u);
v_bs_x27_3305_ = lean_array_uset(v_bs_3290_, v_i_3289_, v___x_3304_);
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_add(v_i_3289_, v___x_3306_);
v___x_3308_ = lean_array_uset(v_bs_x27_3305_, v_i_3289_, v_a_3303_);
v_i_3289_ = v___x_3307_;
v_bs_3290_ = v___x_3308_;
goto _start;
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec_ref(v_bs_3290_);
v_a_3310_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3302_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3302_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(lean_object* v_sz_3318_, lean_object* v_i_3319_, lean_object* v_bs_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
size_t v_sz_boxed_3329_; size_t v_i_boxed_3330_; lean_object* v_res_3331_; 
v_sz_boxed_3329_ = lean_unbox_usize(v_sz_3318_);
lean_dec(v_sz_3318_);
v_i_boxed_3330_ = lean_unbox_usize(v_i_3319_);
lean_dec(v_i_3319_);
v_res_3331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_3329_, v_i_boxed_3330_, v_bs_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract(lean_object* v_es_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; uint8_t v_merge_3352_; 
v_merge_3352_ = lean_ctor_get_uint8(v_a_3333_, 6);
if (v_merge_3352_ == 0)
{
v___y_3342_ = v_a_3333_;
v___y_3343_ = v_a_3334_;
v___y_3344_ = v_a_3335_;
v___y_3345_ = v_a_3336_;
v___y_3346_ = v_a_3337_;
v___y_3347_ = v_a_3338_;
v___y_3348_ = v_a_3339_;
goto v___jp_3341_;
}
else
{
uint8_t v_useContext_3353_; 
v_useContext_3353_ = lean_ctor_get_uint8(v_a_3333_, 7);
if (v_useContext_3353_ == 0)
{
v___y_3342_ = v_a_3333_;
v___y_3343_ = v_a_3334_;
v___y_3344_ = v_a_3335_;
v___y_3345_ = v_a_3336_;
v___y_3346_ = v_a_3337_;
v___y_3347_ = v_a_3338_;
v___y_3348_ = v_a_3339_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3354_; 
lean_inc_ref(v_a_3336_);
v___x_3354_ = l_Lean_Meta_ExtractLets_initializeValueMap(v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_dec_ref(v___x_3354_);
v___y_3342_ = v_a_3333_;
v___y_3343_ = v_a_3334_;
v___y_3344_ = v_a_3335_;
v___y_3345_ = v_a_3336_;
v___y_3346_ = v_a_3337_;
v___y_3347_ = v_a_3338_;
v___y_3348_ = v_a_3339_;
goto v___jp_3341_;
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec_ref(v_es_3332_);
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
v___jp_3341_:
{
size_t v_sz_3349_; size_t v___x_3350_; lean_object* v___x_3351_; 
v_sz_3349_ = lean_array_size(v_es_3332_);
v___x_3350_ = ((size_t)0ULL);
v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_3349_, v___x_3350_, v_es_3332_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ExtractLets_extract___boxed(lean_object* v_es_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Meta_ExtractLets_extract(v_es_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(lean_object* v_decls_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_3373_, v_x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
v_a_3389_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3380_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3380_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(lean_object* v_decls_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3397_, v_x_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(lean_object* v_00_u03b1_3405_, lean_object* v_decls_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_3406_, v_x_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(lean_object* v_00_u03b1_3414_, lean_object* v_decls_3415_, lean_object* v_x_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_3414_, v_decls_3415_, v_x_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(size_t v_sz_3423_, size_t v_i_3424_, lean_object* v_bs_3425_){
_start:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_usize_dec_lt(v_i_3424_, v_sz_3423_);
if (v___x_3426_ == 0)
{
return v_bs_3425_;
}
else
{
lean_object* v_v_3427_; lean_object* v___x_3428_; lean_object* v_bs_x27_3429_; lean_object* v___x_3430_; size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v_v_3427_ = lean_array_uget(v_bs_3425_, v_i_3424_);
v___x_3428_ = lean_unsigned_to_nat(0u);
v_bs_x27_3429_ = lean_array_uset(v_bs_3425_, v_i_3424_, v___x_3428_);
v___x_3430_ = l_Lean_LocalDecl_fvarId(v_v_3427_);
lean_dec(v_v_3427_);
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3424_, v___x_3431_);
v___x_3433_ = lean_array_uset(v_bs_x27_3429_, v_i_3424_, v___x_3430_);
v_i_3424_ = v___x_3432_;
v_bs_3425_ = v___x_3433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(lean_object* v_sz_3435_, lean_object* v_i_3436_, lean_object* v_bs_3437_){
_start:
{
size_t v_sz_boxed_3438_; size_t v_i_boxed_3439_; lean_object* v_res_3440_; 
v_sz_boxed_3438_ = lean_unbox_usize(v_sz_3435_);
lean_dec(v_sz_3435_);
v_i_boxed_3439_ = lean_unbox_usize(v_i_3436_);
lean_dec(v_i_3436_);
v_res_3440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_3438_, v_i_boxed_3439_, v_bs_3437_);
return v_res_3440_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_unsigned_to_nat(16u);
v___x_3443_ = lean_mk_array(v___x_3442_, v___x_3441_);
return v___x_3443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0);
v___x_3445_ = lean_unsigned_to_nat(0u);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v___x_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(lean_object* v_es_3447_, lean_object* v_givenNames_3448_, lean_object* v_k_3449_, lean_object* v_config_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3457_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_3458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3458_, 0, v_givenNames_3448_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
lean_ctor_set(v___x_3458_, 2, v___x_3456_);
v___x_3459_ = lean_st_mk_ref(v___x_3458_);
v___x_3460_ = lean_st_mk_ref(v___x_3456_);
lean_inc(v_a_3454_);
lean_inc_ref(v_a_3453_);
lean_inc(v_a_3452_);
lean_inc_ref(v_a_3451_);
lean_inc(v___x_3459_);
lean_inc(v___x_3460_);
v___x_3461_ = l_Lean_Meta_ExtractLets_extract(v_es_3447_, v_config_3450_, v___x_3460_, v___x_3459_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v_givenNames_3465_; lean_object* v_decls_3466_; size_t v_sz_3467_; size_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; size_t v_sz_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = lean_st_ref_get(v___x_3460_);
lean_dec(v___x_3460_);
lean_dec(v___x_3463_);
v___x_3464_ = lean_st_ref_get(v___x_3459_);
lean_dec(v___x_3459_);
v_givenNames_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_givenNames_3465_);
v_decls_3466_ = lean_ctor_get(v___x_3464_, 1);
lean_inc_ref(v_decls_3466_);
lean_dec(v___x_3464_);
v_sz_3467_ = lean_array_size(v_decls_3466_);
v___x_3468_ = ((size_t)0ULL);
v___x_3469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0_spec__0(v_sz_3467_, v___x_3468_, v_decls_3466_);
lean_inc_ref(v___x_3469_);
v___x_3470_ = lean_array_to_list(v___x_3469_);
v_sz_3471_ = lean_array_size(v___x_3469_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_3471_, v___x_3468_, v___x_3469_);
v___x_3473_ = lean_apply_3(v_k_3449_, v___x_3472_, v_a_3462_, v_givenNames_3465_);
v___x_3474_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_3470_, v___x_3473_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
return v___x_3474_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v___x_3460_);
lean_dec(v___x_3459_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec_ref(v_k_3449_);
v_a_3475_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3461_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3461_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(lean_object* v_es_3483_, lean_object* v_givenNames_3484_, lean_object* v_k_3485_, lean_object* v_config_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3483_, v_givenNames_3484_, v_k_3485_, v_config_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object* v_00_u03b1_3493_, lean_object* v_es_3494_, lean_object* v_givenNames_3495_, lean_object* v_k_3496_, lean_object* v_config_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3494_, v_givenNames_3495_, v_k_3496_, v_config_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(lean_object* v_00_u03b1_3504_, lean_object* v_es_3505_, lean_object* v_givenNames_3506_, lean_object* v_k_3507_, lean_object* v_config_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(v_00_u03b1_3504_, v_es_3505_, v_givenNames_3506_, v_k_3507_, v_config_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0(lean_object* v_k_3515_, lean_object* v_runInBase_3516_, lean_object* v_b_3517_, lean_object* v_c_3518_, lean_object* v_d_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_apply_3(v_k_3515_, v_b_3517_, v_c_3518_, v_d_3519_);
v___x_3526_ = lean_apply_7(v_runInBase_3516_, lean_box(0), v___x_3525_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, lean_box(0));
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__0___boxed(lean_object* v_k_3527_, lean_object* v_runInBase_3528_, lean_object* v_b_3529_, lean_object* v_c_3530_, lean_object* v_d_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Meta_extractLets___redArg___lam__0(v_k_3527_, v_runInBase_3528_, v_b_3529_, v_c_3530_, v_d_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1(lean_object* v_k_3538_, lean_object* v_es_3539_, lean_object* v_givenNames_3540_, lean_object* v_config_3541_, lean_object* v_runInBase_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___f_3548_; lean_object* v___x_3549_; 
v___f_3548_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3548_, 0, v_k_3538_);
lean_closure_set(v___f_3548_, 1, v_runInBase_3542_);
v___x_3549_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3539_, v_givenNames_3540_, v___f_3548_, v_config_3541_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg___lam__1___boxed(lean_object* v_k_3550_, lean_object* v_es_3551_, lean_object* v_givenNames_3552_, lean_object* v_config_3553_, lean_object* v_runInBase_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Meta_extractLets___redArg___lam__1(v_k_3550_, v_es_3551_, v_givenNames_3552_, v_config_3553_, v_runInBase_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___redArg(lean_object* v_inst_3561_, lean_object* v_inst_3562_, lean_object* v_es_3563_, lean_object* v_givenNames_3564_, lean_object* v_k_3565_, lean_object* v_config_3566_){
_start:
{
lean_object* v_toBind_3567_; lean_object* v_liftWith_3568_; lean_object* v_restoreM_3569_; lean_object* v___f_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_toBind_3567_ = lean_ctor_get(v_inst_3561_, 1);
lean_inc(v_toBind_3567_);
lean_dec_ref(v_inst_3561_);
v_liftWith_3568_ = lean_ctor_get(v_inst_3562_, 0);
lean_inc(v_liftWith_3568_);
v_restoreM_3569_ = lean_ctor_get(v_inst_3562_, 1);
lean_inc(v_restoreM_3569_);
lean_dec_ref(v_inst_3562_);
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3570_, 0, v_k_3565_);
lean_closure_set(v___f_3570_, 1, v_es_3563_);
lean_closure_set(v___f_3570_, 2, v_givenNames_3564_);
lean_closure_set(v___f_3570_, 3, v_config_3566_);
v___x_3571_ = lean_apply_2(v_liftWith_3568_, lean_box(0), v___f_3570_);
v___x_3572_ = lean_apply_1(v_restoreM_3569_, lean_box(0));
v___x_3573_ = lean_apply_4(v_toBind_3567_, lean_box(0), lean_box(0), v___x_3571_, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets(lean_object* v_m_3574_, lean_object* v_00_u03b1_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_, lean_object* v_es_3578_, lean_object* v_givenNames_3579_, lean_object* v_k_3580_, lean_object* v_config_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_Meta_extractLets___redArg(v_inst_3576_, v_inst_3577_, v_es_3578_, v_givenNames_3579_, v_k_3580_, v_config_3581_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_Meta_liftLets___closed__0(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3584_ = ((lean_object*)(l_Lean_Meta_ExtractLets_flushDecls___closed__0));
v___x_3585_ = lean_box(0);
v___x_3586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
lean_ctor_set(v___x_3586_, 1, v___x_3584_);
lean_ctor_set(v___x_3586_, 2, v___x_3583_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets(lean_object* v_e_3587_, lean_object* v_config_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v_proofs_3599_; uint8_t v_types_3600_; uint8_t v_implicits_3601_; uint8_t v_descend_3602_; uint8_t v_underBinder_3603_; uint8_t v_usedOnly_3604_; uint8_t v_merge_3605_; uint8_t v_useContext_3606_; uint8_t v_preserveBinderNames_3607_; uint8_t v_lift_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3642_; 
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
v___x_3596_ = lean_obj_once(&l_Lean_Meta_liftLets___closed__0, &l_Lean_Meta_liftLets___closed__0_once, _init_l_Lean_Meta_liftLets___closed__0);
v___x_3597_ = lean_st_mk_ref(v___x_3596_);
v___x_3598_ = lean_st_mk_ref(v___x_3595_);
v_proofs_3599_ = lean_ctor_get_uint8(v_config_3588_, 0);
v_types_3600_ = lean_ctor_get_uint8(v_config_3588_, 1);
v_implicits_3601_ = lean_ctor_get_uint8(v_config_3588_, 2);
v_descend_3602_ = lean_ctor_get_uint8(v_config_3588_, 3);
v_underBinder_3603_ = lean_ctor_get_uint8(v_config_3588_, 4);
v_usedOnly_3604_ = lean_ctor_get_uint8(v_config_3588_, 5);
v_merge_3605_ = lean_ctor_get_uint8(v_config_3588_, 6);
v_useContext_3606_ = lean_ctor_get_uint8(v_config_3588_, 7);
v_preserveBinderNames_3607_ = lean_ctor_get_uint8(v_config_3588_, 9);
v_lift_3608_ = lean_ctor_get_uint8(v_config_3588_, 10);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_config_3588_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3610_ = v_config_3588_;
v_isShared_3611_ = v_isSharedCheck_3642_;
goto v_resetjp_3609_;
}
else
{
lean_dec(v_config_3588_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3642_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; lean_object* v___x_3617_; 
v___x_3612_ = lean_unsigned_to_nat(1u);
v___x_3613_ = lean_mk_empty_array_with_capacity(v___x_3612_);
v___x_3614_ = lean_array_push(v___x_3613_, v_e_3587_);
v___x_3615_ = 1;
if (v_isShared_3611_ == 0)
{
v___x_3617_ = v___x_3610_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 0, v_proofs_3599_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 1, v_types_3600_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 2, v_implicits_3601_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 3, v_descend_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 4, v_underBinder_3603_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 5, v_usedOnly_3604_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 6, v_merge_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 7, v_useContext_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 9, v_preserveBinderNames_3607_);
lean_ctor_set_uint8(v_reuseFailAlloc_3641_, 10, v_lift_3608_);
v___x_3617_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; 
lean_ctor_set_uint8(v___x_3617_, 8, v___x_3615_);
lean_inc(v___x_3597_);
lean_inc(v___x_3598_);
v___x_3618_ = l_Lean_Meta_ExtractLets_extract(v___x_3614_, v___x_3617_, v___x_3598_, v___x_3597_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3632_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3632_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3632_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v_decls_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3623_ = lean_st_ref_get(v___x_3598_);
lean_dec(v___x_3598_);
lean_dec(v___x_3623_);
v___x_3624_ = lean_st_ref_get(v___x_3597_);
lean_dec(v___x_3597_);
v_decls_3625_ = lean_ctor_get(v___x_3624_, 1);
lean_inc_ref(v_decls_3625_);
lean_dec(v___x_3624_);
v___x_3626_ = l_Lean_instInhabitedExpr;
v___x_3627_ = lean_array_get(v___x_3626_, v_a_3619_, v___x_3594_);
lean_dec(v_a_3619_);
v___x_3628_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_3625_, v___x_3627_);
lean_dec_ref(v_decls_3625_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v___x_3628_);
v___x_3630_ = v___x_3621_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___x_3598_);
lean_dec(v___x_3597_);
v_a_3633_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3618_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3618_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_liftLets___boxed(lean_object* v_e_3643_, lean_object* v_config_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Meta_liftLets(v_e_3643_, v_config_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
return v_res_3650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(lean_object* v_tactic_3656_, lean_object* v_mvarId_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2, &l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2);
v___x_3664_ = l_Lean_Meta_throwTacticEx___redArg(v_tactic_3656_, v_mvarId_3657_, v___x_3663_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(lean_object* v_tactic_3665_, lean_object* v_mvarId_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3665_, v_mvarId_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(lean_object* v_00_u03b1_3673_, lean_object* v_tactic_3674_, lean_object* v_mvarId_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v_tactic_3674_, v_mvarId_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_tactic_3683_, lean_object* v_mvarId_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(v_00_u03b1_3682_, v_tactic_3683_, v_mvarId_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(lean_object* v_k_3691_, lean_object* v_b_3692_, lean_object* v_c_3693_, lean_object* v_d_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_apply_8(v_k_3691_, v_b_3692_, v_c_3693_, v_d_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, lean_box(0));
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(lean_object* v_k_3701_, lean_object* v_b_3702_, lean_object* v_c_3703_, lean_object* v_d_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(v_k_3701_, v_b_3702_, v_c_3703_, v_d_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(lean_object* v_es_3711_, lean_object* v_givenNames_3712_, lean_object* v_k_3713_, lean_object* v_config_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___f_3720_; lean_object* v___x_3721_; 
v___f_3720_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3720_, 0, v_k_3713_);
v___x_3721_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(v_es_3711_, v_givenNames_3712_, v___f_3720_, v_config_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
v_a_3730_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3721_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3721_);
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
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(lean_object* v_es_3738_, lean_object* v_givenNames_3739_, lean_object* v_k_3740_, lean_object* v_config_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3738_, v_givenNames_3739_, v_k_3740_, v_config_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(lean_object* v_00_u03b1_3748_, lean_object* v_es_3749_, lean_object* v_givenNames_3750_, lean_object* v_k_3751_, lean_object* v_config_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v_es_3749_, v_givenNames_3750_, v_k_3751_, v_config_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(lean_object* v_00_u03b1_3759_, lean_object* v_es_3760_, lean_object* v_givenNames_3761_, lean_object* v_k_3762_, lean_object* v_config_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(v_00_u03b1_3759_, v_es_3760_, v_givenNames_3761_, v_k_3762_, v_config_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(lean_object* v_mvarId_3770_, lean_object* v_x_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3770_, v_x_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_a_3786_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3777_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3777_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(lean_object* v_mvarId_3794_, lean_object* v_x_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3794_, v_x_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(lean_object* v_00_u03b1_3802_, lean_object* v_mvarId_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_3803_, v_x_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(lean_object* v_00_u03b1_3811_, lean_object* v_mvarId_3812_, lean_object* v_x_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(v_00_u03b1_3811_, v_mvarId_3812_, v_x_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_3820_, lean_object* v_x_3821_, lean_object* v_x_3822_, lean_object* v_x_3823_){
_start:
{
lean_object* v_ks_3824_; lean_object* v_vs_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3849_; 
v_ks_3824_ = lean_ctor_get(v_x_3820_, 0);
v_vs_3825_ = lean_ctor_get(v_x_3820_, 1);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_x_3820_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3827_ = v_x_3820_;
v_isShared_3828_ = v_isSharedCheck_3849_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_vs_3825_);
lean_inc(v_ks_3824_);
lean_dec(v_x_3820_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3849_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; uint8_t v___x_3830_; 
v___x_3829_ = lean_array_get_size(v_ks_3824_);
v___x_3830_ = lean_nat_dec_lt(v_x_3821_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec(v_x_3821_);
v___x_3831_ = lean_array_push(v_ks_3824_, v_x_3822_);
v___x_3832_ = lean_array_push(v_vs_3825_, v_x_3823_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 1, v___x_3832_);
lean_ctor_set(v___x_3827_, 0, v___x_3831_);
v___x_3834_ = v___x_3827_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
else
{
lean_object* v_k_x27_3836_; uint8_t v___x_3837_; 
v_k_x27_3836_ = lean_array_fget_borrowed(v_ks_3824_, v_x_3821_);
v___x_3837_ = l_Lean_instBEqMVarId_beq(v_x_3822_, v_k_x27_3836_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3839_; 
if (v_isShared_3828_ == 0)
{
v___x_3839_ = v___x_3827_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_ks_3824_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_vs_3825_);
v___x_3839_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = lean_unsigned_to_nat(1u);
v___x_3841_ = lean_nat_add(v_x_3821_, v___x_3840_);
lean_dec(v_x_3821_);
v_x_3820_ = v___x_3839_;
v_x_3821_ = v___x_3841_;
goto _start;
}
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3844_ = lean_array_fset(v_ks_3824_, v_x_3821_, v_x_3822_);
v___x_3845_ = lean_array_fset(v_vs_3825_, v_x_3821_, v_x_3823_);
lean_dec(v_x_3821_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 1, v___x_3845_);
lean_ctor_set(v___x_3827_, 0, v___x_3844_);
v___x_3847_ = v___x_3827_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_n_3850_, lean_object* v_k_3851_, lean_object* v_v_3852_){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_unsigned_to_nat(0u);
v___x_3854_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_3850_, v___x_3853_, v_k_3851_, v_v_3852_);
return v___x_3854_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_3855_; size_t v___x_3856_; size_t v___x_3857_; 
v___x_3855_ = ((size_t)5ULL);
v___x_3856_ = ((size_t)1ULL);
v___x_3857_ = lean_usize_shift_left(v___x_3856_, v___x_3855_);
return v___x_3857_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3858_; size_t v___x_3859_; size_t v___x_3860_; 
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
v___x_3860_ = lean_usize_sub(v___x_3859_, v___x_3858_);
return v___x_3860_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(lean_object* v_x_3862_, size_t v_x_3863_, size_t v_x_3864_, lean_object* v_x_3865_, lean_object* v_x_3866_){
_start:
{
if (lean_obj_tag(v_x_3862_) == 0)
{
lean_object* v_es_3867_; size_t v___x_3868_; size_t v___x_3869_; size_t v___x_3870_; size_t v___x_3871_; lean_object* v_j_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v_es_3867_ = lean_ctor_get(v_x_3862_, 0);
v___x_3868_ = ((size_t)5ULL);
v___x_3869_ = ((size_t)1ULL);
v___x_3870_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1);
v___x_3871_ = lean_usize_land(v_x_3863_, v___x_3870_);
v_j_3872_ = lean_usize_to_nat(v___x_3871_);
v___x_3873_ = lean_array_get_size(v_es_3867_);
v___x_3874_ = lean_nat_dec_lt(v_j_3872_, v___x_3873_);
if (v___x_3874_ == 0)
{
lean_dec(v_j_3872_);
lean_dec(v_x_3866_);
lean_dec(v_x_3865_);
return v_x_3862_;
}
else
{
lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3911_; 
lean_inc_ref(v_es_3867_);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_x_3862_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v_x_3862_, 0);
lean_dec(v_unused_3912_);
v___x_3876_ = v_x_3862_;
v_isShared_3877_ = v_isSharedCheck_3911_;
goto v_resetjp_3875_;
}
else
{
lean_dec(v_x_3862_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3911_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v_v_3878_; lean_object* v___x_3879_; lean_object* v_xs_x27_3880_; lean_object* v___y_3882_; 
v_v_3878_ = lean_array_fget(v_es_3867_, v_j_3872_);
v___x_3879_ = lean_box(0);
v_xs_x27_3880_ = lean_array_fset(v_es_3867_, v_j_3872_, v___x_3879_);
switch(lean_obj_tag(v_v_3878_))
{
case 0:
{
lean_object* v_key_3887_; lean_object* v_val_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3898_; 
v_key_3887_ = lean_ctor_get(v_v_3878_, 0);
v_val_3888_ = lean_ctor_get(v_v_3878_, 1);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_v_3878_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3890_ = v_v_3878_;
v_isShared_3891_ = v_isSharedCheck_3898_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_val_3888_);
lean_inc(v_key_3887_);
lean_dec(v_v_3878_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3898_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
uint8_t v___x_3892_; 
v___x_3892_ = l_Lean_instBEqMVarId_beq(v_x_3865_, v_key_3887_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_del_object(v___x_3890_);
v___x_3893_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3887_, v_val_3888_, v_x_3865_, v_x_3866_);
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
v___y_3882_ = v___x_3894_;
goto v___jp_3881_;
}
else
{
lean_object* v___x_3896_; 
lean_dec(v_val_3888_);
lean_dec(v_key_3887_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 1, v_x_3866_);
lean_ctor_set(v___x_3890_, 0, v_x_3865_);
v___x_3896_ = v___x_3890_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_x_3865_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_x_3866_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
v___y_3882_ = v___x_3896_;
goto v___jp_3881_;
}
}
}
}
case 1:
{
lean_object* v_node_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3909_; 
v_node_3899_ = lean_ctor_get(v_v_3878_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_v_3878_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3901_ = v_v_3878_;
v_isShared_3902_ = v_isSharedCheck_3909_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_node_3899_);
lean_dec(v_v_3878_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3909_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
size_t v___x_3903_; size_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3903_ = lean_usize_shift_right(v_x_3863_, v___x_3868_);
v___x_3904_ = lean_usize_add(v_x_3864_, v___x_3869_);
v___x_3905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_3899_, v___x_3903_, v___x_3904_, v_x_3865_, v_x_3866_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3905_);
v___x_3907_ = v___x_3901_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
v___y_3882_ = v___x_3907_;
goto v___jp_3881_;
}
}
}
default: 
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3910_, 0, v_x_3865_);
lean_ctor_set(v___x_3910_, 1, v_x_3866_);
v___y_3882_ = v___x_3910_;
goto v___jp_3881_;
}
}
v___jp_3881_:
{
lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3883_ = lean_array_fset(v_xs_x27_3880_, v_j_3872_, v___y_3882_);
lean_dec(v_j_3872_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v___x_3883_);
v___x_3885_ = v___x_3876_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
else
{
lean_object* v_ks_3913_; lean_object* v_vs_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3934_; 
v_ks_3913_ = lean_ctor_get(v_x_3862_, 0);
v_vs_3914_ = lean_ctor_get(v_x_3862_, 1);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_x_3862_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3916_ = v_x_3862_;
v_isShared_3917_ = v_isSharedCheck_3934_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_vs_3914_);
lean_inc(v_ks_3913_);
lean_dec(v_x_3862_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3934_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_ks_3913_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_vs_3914_);
v___x_3919_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v_newNode_3920_; uint8_t v___y_3922_; size_t v___x_3928_; uint8_t v___x_3929_; 
v_newNode_3920_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_3919_, v_x_3865_, v_x_3866_);
v___x_3928_ = ((size_t)7ULL);
v___x_3929_ = lean_usize_dec_le(v___x_3928_, v_x_3864_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; uint8_t v___x_3932_; 
v___x_3930_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3920_);
v___x_3931_ = lean_unsigned_to_nat(4u);
v___x_3932_ = lean_nat_dec_lt(v___x_3930_, v___x_3931_);
lean_dec(v___x_3930_);
v___y_3922_ = v___x_3932_;
goto v___jp_3921_;
}
else
{
v___y_3922_ = v___x_3929_;
goto v___jp_3921_;
}
v___jp_3921_:
{
if (v___y_3922_ == 0)
{
lean_object* v_ks_3923_; lean_object* v_vs_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_ks_3923_ = lean_ctor_get(v_newNode_3920_, 0);
lean_inc_ref(v_ks_3923_);
v_vs_3924_ = lean_ctor_get(v_newNode_3920_, 1);
lean_inc_ref(v_vs_3924_);
lean_dec_ref(v_newNode_3920_);
v___x_3925_ = lean_unsigned_to_nat(0u);
v___x_3926_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_3927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_3864_, v_ks_3923_, v_vs_3924_, v___x_3925_, v___x_3926_);
lean_dec_ref(v_vs_3924_);
lean_dec_ref(v_ks_3923_);
return v___x_3927_;
}
else
{
return v_newNode_3920_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(size_t v_depth_3935_, lean_object* v_keys_3936_, lean_object* v_vals_3937_, lean_object* v_i_3938_, lean_object* v_entries_3939_){
_start:
{
lean_object* v___x_3940_; uint8_t v___x_3941_; 
v___x_3940_ = lean_array_get_size(v_keys_3936_);
v___x_3941_ = lean_nat_dec_lt(v_i_3938_, v___x_3940_);
if (v___x_3941_ == 0)
{
lean_dec(v_i_3938_);
return v_entries_3939_;
}
else
{
lean_object* v_k_3942_; lean_object* v_v_3943_; uint64_t v___x_3944_; size_t v_h_3945_; size_t v___x_3946_; lean_object* v___x_3947_; size_t v___x_3948_; size_t v___x_3949_; size_t v___x_3950_; size_t v_h_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_k_3942_ = lean_array_fget_borrowed(v_keys_3936_, v_i_3938_);
v_v_3943_ = lean_array_fget_borrowed(v_vals_3937_, v_i_3938_);
v___x_3944_ = l_Lean_instHashableMVarId_hash(v_k_3942_);
v_h_3945_ = lean_uint64_to_usize(v___x_3944_);
v___x_3946_ = ((size_t)5ULL);
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = ((size_t)1ULL);
v___x_3949_ = lean_usize_sub(v_depth_3935_, v___x_3948_);
v___x_3950_ = lean_usize_mul(v___x_3946_, v___x_3949_);
v_h_3951_ = lean_usize_shift_right(v_h_3945_, v___x_3950_);
v___x_3952_ = lean_nat_add(v_i_3938_, v___x_3947_);
lean_dec(v_i_3938_);
lean_inc(v_v_3943_);
lean_inc(v_k_3942_);
v___x_3953_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_3939_, v_h_3951_, v_depth_3935_, v_k_3942_, v_v_3943_);
v_i_3938_ = v___x_3952_;
v_entries_3939_ = v___x_3953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_depth_3955_, lean_object* v_keys_3956_, lean_object* v_vals_3957_, lean_object* v_i_3958_, lean_object* v_entries_3959_){
_start:
{
size_t v_depth_boxed_3960_; lean_object* v_res_3961_; 
v_depth_boxed_3960_ = lean_unbox_usize(v_depth_3955_);
lean_dec(v_depth_3955_);
v_res_3961_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_3960_, v_keys_3956_, v_vals_3957_, v_i_3958_, v_entries_3959_);
lean_dec_ref(v_vals_3957_);
lean_dec_ref(v_keys_3956_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_x_3962_, lean_object* v_x_3963_, lean_object* v_x_3964_, lean_object* v_x_3965_, lean_object* v_x_3966_){
_start:
{
size_t v_x_2416__boxed_3967_; size_t v_x_2417__boxed_3968_; lean_object* v_res_3969_; 
v_x_2416__boxed_3967_ = lean_unbox_usize(v_x_3963_);
lean_dec(v_x_3963_);
v_x_2417__boxed_3968_ = lean_unbox_usize(v_x_3964_);
lean_dec(v_x_3964_);
v_res_3969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3962_, v_x_2416__boxed_3967_, v_x_2417__boxed_3968_, v_x_3965_, v_x_3966_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(lean_object* v_x_3970_, lean_object* v_x_3971_, lean_object* v_x_3972_){
_start:
{
uint64_t v___x_3973_; size_t v___x_3974_; size_t v___x_3975_; lean_object* v___x_3976_; 
v___x_3973_ = l_Lean_instHashableMVarId_hash(v_x_3971_);
v___x_3974_ = lean_uint64_to_usize(v___x_3973_);
v___x_3975_ = ((size_t)1ULL);
v___x_3976_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_3970_, v___x_3974_, v___x_3975_, v_x_3971_, v_x_3972_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(lean_object* v_mvarId_3977_, lean_object* v_val_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v___x_3981_; lean_object* v_mctx_3982_; lean_object* v_cache_3983_; lean_object* v_zetaDeltaFVarIds_3984_; lean_object* v_postponed_3985_; lean_object* v_diag_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4013_; 
v___x_3981_ = lean_st_ref_take(v___y_3979_);
v_mctx_3982_ = lean_ctor_get(v___x_3981_, 0);
v_cache_3983_ = lean_ctor_get(v___x_3981_, 1);
v_zetaDeltaFVarIds_3984_ = lean_ctor_get(v___x_3981_, 2);
v_postponed_3985_ = lean_ctor_get(v___x_3981_, 3);
v_diag_3986_ = lean_ctor_get(v___x_3981_, 4);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3988_ = v___x_3981_;
v_isShared_3989_ = v_isSharedCheck_4013_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_diag_3986_);
lean_inc(v_postponed_3985_);
lean_inc(v_zetaDeltaFVarIds_3984_);
lean_inc(v_cache_3983_);
lean_inc(v_mctx_3982_);
lean_dec(v___x_3981_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4013_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v_depth_3990_; lean_object* v_levelAssignDepth_3991_; lean_object* v_mvarCounter_3992_; lean_object* v_lDepth_3993_; lean_object* v_decls_3994_; lean_object* v_userNames_3995_; lean_object* v_lAssignment_3996_; lean_object* v_eAssignment_3997_; lean_object* v_dAssignment_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4012_; 
v_depth_3990_ = lean_ctor_get(v_mctx_3982_, 0);
v_levelAssignDepth_3991_ = lean_ctor_get(v_mctx_3982_, 1);
v_mvarCounter_3992_ = lean_ctor_get(v_mctx_3982_, 2);
v_lDepth_3993_ = lean_ctor_get(v_mctx_3982_, 3);
v_decls_3994_ = lean_ctor_get(v_mctx_3982_, 4);
v_userNames_3995_ = lean_ctor_get(v_mctx_3982_, 5);
v_lAssignment_3996_ = lean_ctor_get(v_mctx_3982_, 6);
v_eAssignment_3997_ = lean_ctor_get(v_mctx_3982_, 7);
v_dAssignment_3998_ = lean_ctor_get(v_mctx_3982_, 8);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_mctx_3982_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4000_ = v_mctx_3982_;
v_isShared_4001_ = v_isSharedCheck_4012_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_dAssignment_3998_);
lean_inc(v_eAssignment_3997_);
lean_inc(v_lAssignment_3996_);
lean_inc(v_userNames_3995_);
lean_inc(v_decls_3994_);
lean_inc(v_lDepth_3993_);
lean_inc(v_mvarCounter_3992_);
lean_inc(v_levelAssignDepth_3991_);
lean_inc(v_depth_3990_);
lean_dec(v_mctx_3982_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4012_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_4002_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_3997_, v_mvarId_3977_, v_val_3978_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 7, v___x_4002_);
v___x_4004_ = v___x_4000_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_depth_3990_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_levelAssignDepth_3991_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_mvarCounter_3992_);
lean_ctor_set(v_reuseFailAlloc_4011_, 3, v_lDepth_3993_);
lean_ctor_set(v_reuseFailAlloc_4011_, 4, v_decls_3994_);
lean_ctor_set(v_reuseFailAlloc_4011_, 5, v_userNames_3995_);
lean_ctor_set(v_reuseFailAlloc_4011_, 6, v_lAssignment_3996_);
lean_ctor_set(v_reuseFailAlloc_4011_, 7, v___x_4002_);
lean_ctor_set(v_reuseFailAlloc_4011_, 8, v_dAssignment_3998_);
v___x_4004_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4006_; 
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_4004_);
v___x_4006_ = v___x_3988_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v_cache_3983_);
lean_ctor_set(v_reuseFailAlloc_4010_, 2, v_zetaDeltaFVarIds_3984_);
lean_ctor_set(v_reuseFailAlloc_4010_, 3, v_postponed_3985_);
lean_ctor_set(v_reuseFailAlloc_4010_, 4, v_diag_3986_);
v___x_4006_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4007_ = lean_st_ref_set(v___y_3979_, v___x_4006_);
v___x_4008_ = lean_box(0);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(lean_object* v_mvarId_4014_, lean_object* v_val_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4014_, v_val_4015_, v___y_4016_);
lean_dec(v___y_4016_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(size_t v_sz_4019_, size_t v_i_4020_, lean_object* v_bs_4021_){
_start:
{
uint8_t v___x_4022_; 
v___x_4022_ = lean_usize_dec_lt(v_i_4020_, v_sz_4019_);
if (v___x_4022_ == 0)
{
return v_bs_4021_;
}
else
{
lean_object* v_v_4023_; lean_object* v___x_4024_; lean_object* v_bs_x27_4025_; lean_object* v___x_4026_; size_t v___x_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v_v_4023_ = lean_array_uget(v_bs_4021_, v_i_4020_);
v___x_4024_ = lean_unsigned_to_nat(0u);
v_bs_x27_4025_ = lean_array_uset(v_bs_4021_, v_i_4020_, v___x_4024_);
v___x_4026_ = l_Lean_Expr_fvar___override(v_v_4023_);
v___x_4027_ = ((size_t)1ULL);
v___x_4028_ = lean_usize_add(v_i_4020_, v___x_4027_);
v___x_4029_ = lean_array_uset(v_bs_x27_4025_, v_i_4020_, v___x_4026_);
v_i_4020_ = v___x_4028_;
v_bs_4021_ = v___x_4029_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(lean_object* v_sz_4031_, lean_object* v_i_4032_, lean_object* v_bs_4033_){
_start:
{
size_t v_sz_boxed_4034_; size_t v_i_boxed_4035_; lean_object* v_res_4036_; 
v_sz_boxed_4034_ = lean_unbox_usize(v_sz_4031_);
lean_dec(v_sz_4031_);
v_i_boxed_4035_ = lean_unbox_usize(v_i_4032_);
lean_dec(v_i_4032_);
v_res_4036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_4034_, v_i_boxed_4035_, v_bs_4033_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0(lean_object* v___x_4037_, lean_object* v_mvarId_4038_, lean_object* v___x_4039_, lean_object* v_a_4040_, lean_object* v_fvarIds_4041_, lean_object* v_es_4042_, lean_object* v_givenNames_x27_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___y_4101_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_array_get_borrowed(v___x_4037_, v_es_4042_, v___x_4049_);
v___x_4111_ = lean_array_get_size(v_fvarIds_4041_);
v___x_4112_ = lean_nat_dec_eq(v___x_4111_, v___x_4049_);
if (v___x_4112_ == 0)
{
v___y_4101_ = v___x_4112_;
goto v___jp_4100_;
}
else
{
uint8_t v___x_4113_; 
v___x_4113_ = lean_expr_eqv(v_a_4040_, v___x_4050_);
v___y_4101_ = v___x_4113_;
goto v___jp_4100_;
}
v___jp_4051_:
{
lean_object* v___x_4052_; 
lean_inc(v_mvarId_4038_);
v___x_4052_ = l_Lean_MVarId_getTag(v_mvarId_4038_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4054_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref(v___x_4052_);
lean_inc_ref(v___y_4044_);
lean_inc(v___x_4050_);
v___x_4054_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_4050_, v_a_4053_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; size_t v_sz_4056_; size_t v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; uint8_t v___x_4060_; uint8_t v___x_4061_; lean_object* v___x_4062_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4055_);
lean_dec_ref(v___x_4054_);
v_sz_4056_ = lean_array_size(v_fvarIds_4041_);
v___x_4057_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4041_);
v___x_4058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4056_, v___x_4057_, v_fvarIds_4041_);
v___x_4059_ = 0;
v___x_4060_ = 1;
v___x_4061_ = 1;
lean_inc(v_a_4055_);
v___x_4062_ = l_Lean_Meta_mkLetFVars(v___x_4058_, v_a_4055_, v___x_4059_, v___x_4060_, v___x_4061_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___x_4058_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4074_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref(v___x_4062_);
v___x_4064_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4038_, v_a_4063_, v___y_4045_);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; 
v_unused_4075_ = lean_ctor_get(v___x_4064_, 0);
lean_dec(v_unused_4075_);
v___x_4066_ = v___x_4064_;
v_isShared_4067_ = v_isSharedCheck_4074_;
goto v_resetjp_4065_;
}
else
{
lean_dec(v___x_4064_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4074_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
v___x_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4068_, 0, v_fvarIds_4041_);
lean_ctor_set(v___x_4068_, 1, v_givenNames_x27_4043_);
v___x_4069_ = l_Lean_Expr_mvarId_x21(v_a_4055_);
lean_dec(v_a_4055_);
v___x_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4070_);
v___x_4072_ = v___x_4066_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec(v_a_4055_);
lean_dec(v_givenNames_x27_4043_);
lean_dec_ref(v_fvarIds_4041_);
lean_dec(v_mvarId_4038_);
v_a_4076_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4062_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4062_);
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
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec_ref(v___y_4044_);
lean_dec(v_givenNames_x27_4043_);
lean_dec_ref(v_fvarIds_4041_);
lean_dec(v_mvarId_4038_);
v_a_4084_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4054_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4054_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v___y_4044_);
lean_dec(v_givenNames_x27_4043_);
lean_dec_ref(v_fvarIds_4041_);
lean_dec(v_mvarId_4038_);
v_a_4092_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4052_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4052_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
v___jp_4100_:
{
if (v___y_4101_ == 0)
{
lean_dec(v___x_4039_);
goto v___jp_4051_;
}
else
{
lean_object* v___x_4102_; 
lean_inc(v_mvarId_4038_);
v___x_4102_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4039_, v_mvarId_4038_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_dec_ref(v___x_4102_);
goto v___jp_4051_;
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec_ref(v___y_4044_);
lean_dec(v_givenNames_x27_4043_);
lean_dec_ref(v_fvarIds_4041_);
lean_dec(v_mvarId_4038_);
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__0___boxed(lean_object* v___x_4114_, lean_object* v_mvarId_4115_, lean_object* v___x_4116_, lean_object* v_a_4117_, lean_object* v_fvarIds_4118_, lean_object* v_es_4119_, lean_object* v_givenNames_x27_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_MVarId_extractLets___lam__0(v___x_4114_, v_mvarId_4115_, v___x_4116_, v_a_4117_, v_fvarIds_4118_, v_es_4119_, v_givenNames_x27_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v_es_4119_);
lean_dec_ref(v_a_4117_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1(lean_object* v_mvarId_4127_, lean_object* v___x_4128_, lean_object* v___x_4129_, lean_object* v_givenNames_4130_, lean_object* v_config_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; 
lean_inc(v___x_4128_);
lean_inc(v_mvarId_4127_);
v___x_4137_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4127_, v___x_4128_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v___x_4138_; 
lean_dec_ref(v___x_4137_);
lean_inc(v_mvarId_4127_);
v___x_4138_ = l_Lean_MVarId_getType(v_mvarId_4127_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___f_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref(v___x_4138_);
lean_inc(v_a_4139_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4140_, 0, v___x_4129_);
lean_closure_set(v___f_4140_, 1, v_mvarId_4127_);
lean_closure_set(v___f_4140_, 2, v___x_4128_);
lean_closure_set(v___f_4140_, 3, v_a_4139_);
v___x_4141_ = lean_unsigned_to_nat(1u);
v___x_4142_ = lean_mk_empty_array_with_capacity(v___x_4141_);
v___x_4143_ = lean_array_push(v___x_4142_, v_a_4139_);
v___x_4144_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4143_, v_givenNames_4130_, v___f_4140_, v_config_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
return v___x_4144_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec_ref(v_config_4131_);
lean_dec(v_givenNames_4130_);
lean_dec_ref(v___x_4129_);
lean_dec(v___x_4128_);
lean_dec(v_mvarId_4127_);
v_a_4145_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4138_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4138_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec_ref(v_config_4131_);
lean_dec(v_givenNames_4130_);
lean_dec_ref(v___x_4129_);
lean_dec(v___x_4128_);
lean_dec(v_mvarId_4127_);
v_a_4153_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4137_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4137_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___lam__1___boxed(lean_object* v_mvarId_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v_givenNames_4164_, lean_object* v_config_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_MVarId_extractLets___lam__1(v_mvarId_4161_, v___x_4162_, v___x_4163_, v_givenNames_4164_, v_config_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets(lean_object* v_mvarId_4175_, lean_object* v_givenNames_4176_, lean_object* v_config_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; 
v___x_4183_ = l_Lean_instInhabitedExpr;
v___x_4184_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4175_);
v___f_4185_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLets___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4185_, 0, v_mvarId_4175_);
lean_closure_set(v___f_4185_, 1, v___x_4184_);
lean_closure_set(v___f_4185_, 2, v___x_4183_);
lean_closure_set(v___f_4185_, 3, v_givenNames_4176_);
lean_closure_set(v___f_4185_, 4, v_config_4177_);
v___x_4186_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4175_, v___f_4185_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLets___boxed(lean_object* v_mvarId_4187_, lean_object* v_givenNames_4188_, lean_object* v_config_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_MVarId_extractLets(v_mvarId_4187_, v_givenNames_4188_, v_config_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(lean_object* v_mvarId_4196_, lean_object* v_val_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4196_, v_val_4197_, v___y_4199_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(lean_object* v_mvarId_4204_, lean_object* v_val_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(v_mvarId_4204_, v_val_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(lean_object* v_00_u03b2_4212_, lean_object* v_x_4213_, lean_object* v_x_4214_, lean_object* v_x_4215_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_4213_, v_x_4214_, v_x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_4217_, lean_object* v_x_4218_, size_t v_x_4219_, size_t v_x_4220_, lean_object* v_x_4221_, lean_object* v_x_4222_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_4218_, v_x_4219_, v_x_4220_, v_x_4221_, v_x_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4224_, lean_object* v_x_4225_, lean_object* v_x_4226_, lean_object* v_x_4227_, lean_object* v_x_4228_, lean_object* v_x_4229_){
_start:
{
size_t v_x_2932__boxed_4230_; size_t v_x_2933__boxed_4231_; lean_object* v_res_4232_; 
v_x_2932__boxed_4230_ = lean_unbox_usize(v_x_4226_);
lean_dec(v_x_4226_);
v_x_2933__boxed_4231_ = lean_unbox_usize(v_x_4227_);
lean_dec(v_x_4227_);
v_res_4232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_4224_, v_x_4225_, v_x_2932__boxed_4230_, v_x_2933__boxed_4231_, v_x_4228_, v_x_4229_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_4233_, lean_object* v_n_4234_, lean_object* v_k_4235_, lean_object* v_v_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_4234_, v_k_4235_, v_v_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_4238_, size_t v_depth_4239_, lean_object* v_keys_4240_, lean_object* v_vals_4241_, lean_object* v_heq_4242_, lean_object* v_i_4243_, lean_object* v_entries_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_4239_, v_keys_4240_, v_vals_4241_, v_i_4243_, v_entries_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4246_, lean_object* v_depth_4247_, lean_object* v_keys_4248_, lean_object* v_vals_4249_, lean_object* v_heq_4250_, lean_object* v_i_4251_, lean_object* v_entries_4252_){
_start:
{
size_t v_depth_boxed_4253_; lean_object* v_res_4254_; 
v_depth_boxed_4253_ = lean_unbox_usize(v_depth_4247_);
lean_dec(v_depth_4247_);
v_res_4254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_4246_, v_depth_boxed_4253_, v_keys_4248_, v_vals_4249_, v_heq_4250_, v_i_4251_, v_entries_4252_);
lean_dec_ref(v_vals_4249_);
lean_dec_ref(v_keys_4248_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_4255_, lean_object* v_x_4256_, lean_object* v_x_4257_, lean_object* v_x_4258_, lean_object* v_x_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_4256_, v_x_4257_, v_x_4258_, v_x_4259_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(size_t v_sz_4261_, size_t v_i_4262_, lean_object* v_bs_4263_){
_start:
{
uint8_t v___x_4264_; 
v___x_4264_ = lean_usize_dec_lt(v_i_4262_, v_sz_4261_);
if (v___x_4264_ == 0)
{
return v_bs_4263_;
}
else
{
lean_object* v_v_4265_; lean_object* v___x_4266_; lean_object* v_bs_x27_4267_; lean_object* v___x_4268_; size_t v___x_4269_; size_t v___x_4270_; lean_object* v___x_4271_; 
v_v_4265_ = lean_array_uget(v_bs_4263_, v_i_4262_);
v___x_4266_ = lean_unsigned_to_nat(0u);
v_bs_x27_4267_ = lean_array_uset(v_bs_4263_, v_i_4262_, v___x_4266_);
v___x_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4268_, 0, v_v_4265_);
v___x_4269_ = ((size_t)1ULL);
v___x_4270_ = lean_usize_add(v_i_4262_, v___x_4269_);
v___x_4271_ = lean_array_uset(v_bs_x27_4267_, v_i_4262_, v___x_4268_);
v_i_4262_ = v___x_4270_;
v_bs_4263_ = v___x_4271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(lean_object* v_sz_4273_, lean_object* v_i_4274_, lean_object* v_bs_4275_){
_start:
{
size_t v_sz_boxed_4276_; size_t v_i_boxed_4277_; lean_object* v_res_4278_; 
v_sz_boxed_4276_ = lean_unbox_usize(v_sz_4273_);
lean_dec(v_sz_4273_);
v_i_boxed_4277_ = lean_unbox_usize(v_i_4274_);
lean_dec(v_i_4274_);
v_res_4278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_4276_, v_i_boxed_4277_, v_bs_4275_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0(lean_object* v_mvarId_4279_, lean_object* v_fvars_4280_, lean_object* v_fvarIds_4281_, lean_object* v_givenNames_x27_4282_, lean_object* v_targetNew_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v___x_4289_; 
lean_inc(v_mvarId_4279_);
v___x_4289_ = l_Lean_MVarId_getTag(v_mvarId_4279_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4291_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4289_);
lean_inc_ref(v___y_4284_);
v___x_4291_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_4283_, v_a_4290_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; size_t v_sz_4293_; size_t v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; uint8_t v___x_4297_; uint8_t v___x_4298_; lean_object* v___x_4299_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref(v___x_4291_);
v_sz_4293_ = lean_array_size(v_fvarIds_4281_);
v___x_4294_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_4281_);
v___x_4295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_4293_, v___x_4294_, v_fvarIds_4281_);
v___x_4296_ = 0;
v___x_4297_ = 1;
v___x_4298_ = 1;
lean_inc(v_a_4292_);
v___x_4299_ = l_Lean_Meta_mkLetFVars(v___x_4295_, v_a_4292_, v___x_4296_, v___x_4297_, v___x_4298_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___x_4295_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4314_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref(v___x_4299_);
v___x_4301_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_4279_, v_a_4300_, v___y_4285_);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4314_ == 0)
{
lean_object* v_unused_4315_; 
v_unused_4315_ = lean_ctor_get(v___x_4301_, 0);
lean_dec(v_unused_4315_);
v___x_4303_ = v___x_4301_;
v_isShared_4304_ = v_isSharedCheck_4314_;
goto v_resetjp_4302_;
}
else
{
lean_dec(v___x_4301_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4314_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; size_t v_sz_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v_fvarIds_4281_);
lean_ctor_set(v___x_4305_, 1, v_givenNames_x27_4282_);
v_sz_4306_ = lean_array_size(v_fvars_4280_);
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4306_, v___x_4294_, v_fvars_4280_);
v___x_4308_ = l_Lean_Expr_mvarId_x21(v_a_4292_);
lean_dec(v_a_4292_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4307_);
lean_ctor_set(v___x_4309_, 1, v___x_4308_);
v___x_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4305_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4310_);
v___x_4312_ = v___x_4303_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec(v_a_4292_);
lean_dec(v_givenNames_x27_4282_);
lean_dec_ref(v_fvarIds_4281_);
lean_dec_ref(v_fvars_4280_);
lean_dec(v_mvarId_4279_);
v_a_4316_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4299_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4299_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec_ref(v___y_4284_);
lean_dec(v_givenNames_x27_4282_);
lean_dec_ref(v_fvarIds_4281_);
lean_dec_ref(v_fvars_4280_);
lean_dec(v_mvarId_4279_);
v_a_4324_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4291_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4291_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
lean_dec_ref(v___y_4284_);
lean_dec_ref(v_targetNew_4283_);
lean_dec(v_givenNames_x27_4282_);
lean_dec_ref(v_fvarIds_4281_);
lean_dec_ref(v_fvars_4280_);
lean_dec(v_mvarId_4279_);
v_a_4332_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4289_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4289_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4340_, lean_object* v_fvars_4341_, lean_object* v_fvarIds_4342_, lean_object* v_givenNames_x27_4343_, lean_object* v_targetNew_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(v_mvarId_4340_, v_fvars_4341_, v_fvarIds_4342_, v_givenNames_x27_4343_, v_targetNew_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1(lean_object* v___x_4351_, lean_object* v_binderName_4352_, lean_object* v_body_4353_, uint8_t v_binderInfo_4354_, lean_object* v___f_4355_, lean_object* v___x_4356_, lean_object* v_mvarId_4357_, lean_object* v_binderType_4358_, lean_object* v_fvarIds_4359_, lean_object* v_es_4360_, lean_object* v_givenNames_x27_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; uint8_t v___y_4373_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4367_ = lean_unsigned_to_nat(0u);
v___x_4368_ = lean_array_get_borrowed(v___x_4351_, v_es_4360_, v___x_4367_);
v___x_4383_ = lean_array_get_size(v_fvarIds_4359_);
v___x_4384_ = lean_nat_dec_eq(v___x_4383_, v___x_4367_);
if (v___x_4384_ == 0)
{
v___y_4373_ = v___x_4384_;
goto v___jp_4372_;
}
else
{
uint8_t v___x_4385_; 
v___x_4385_ = lean_expr_eqv(v_binderType_4358_, v___x_4368_);
v___y_4373_ = v___x_4385_;
goto v___jp_4372_;
}
v___jp_4369_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
lean_inc(v___x_4368_);
v___x_4370_ = l_Lean_Expr_forallE___override(v_binderName_4352_, v___x_4368_, v_body_4353_, v_binderInfo_4354_);
v___x_4371_ = lean_apply_8(v___f_4355_, v_fvarIds_4359_, v_givenNames_x27_4361_, v___x_4370_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, lean_box(0));
return v___x_4371_;
}
v___jp_4372_:
{
if (v___y_4373_ == 0)
{
lean_dec(v_mvarId_4357_);
lean_dec(v___x_4356_);
goto v___jp_4369_;
}
else
{
lean_object* v___x_4374_; 
v___x_4374_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4356_, v_mvarId_4357_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_dec_ref(v___x_4374_);
goto v___jp_4369_;
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v_givenNames_x27_4361_);
lean_dec_ref(v_fvarIds_4359_);
lean_dec_ref(v___f_4355_);
lean_dec_ref(v_body_4353_);
lean_dec(v_binderName_4352_);
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4374_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4374_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(lean_object* v___x_4386_, lean_object* v_binderName_4387_, lean_object* v_body_4388_, lean_object* v_binderInfo_4389_, lean_object* v___f_4390_, lean_object* v___x_4391_, lean_object* v_mvarId_4392_, lean_object* v_binderType_4393_, lean_object* v_fvarIds_4394_, lean_object* v_es_4395_, lean_object* v_givenNames_x27_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
uint8_t v_binderInfo_1887__boxed_4402_; lean_object* v_res_4403_; 
v_binderInfo_1887__boxed_4402_ = lean_unbox(v_binderInfo_4389_);
v_res_4403_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(v___x_4386_, v_binderName_4387_, v_body_4388_, v_binderInfo_1887__boxed_4402_, v___f_4390_, v___x_4391_, v_mvarId_4392_, v_binderType_4393_, v_fvarIds_4394_, v_es_4395_, v_givenNames_x27_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
lean_dec_ref(v_es_4395_);
lean_dec_ref(v_binderType_4393_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2(lean_object* v___x_4404_, lean_object* v_declName_4405_, lean_object* v_body_4406_, uint8_t v_nondep_4407_, lean_object* v___f_4408_, lean_object* v_value_4409_, lean_object* v___x_4410_, lean_object* v_mvarId_4411_, lean_object* v_type_4412_, lean_object* v_fvarIds_4413_, lean_object* v_es_4414_, lean_object* v_givenNames_x27_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___y_4429_; lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4421_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_4404_);
v___x_4422_ = lean_array_get_borrowed(v___x_4404_, v_es_4414_, v___x_4421_);
v___x_4423_ = lean_unsigned_to_nat(1u);
v___x_4424_ = lean_array_get_borrowed(v___x_4404_, v_es_4414_, v___x_4423_);
v___x_4440_ = lean_array_get_size(v_fvarIds_4413_);
v___x_4441_ = lean_nat_dec_eq(v___x_4440_, v___x_4421_);
if (v___x_4441_ == 0)
{
v___y_4429_ = v___x_4441_;
goto v___jp_4428_;
}
else
{
uint8_t v___x_4442_; 
v___x_4442_ = lean_expr_eqv(v_type_4412_, v___x_4422_);
v___y_4429_ = v___x_4442_;
goto v___jp_4428_;
}
v___jp_4425_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
lean_inc(v___x_4424_);
lean_inc(v___x_4422_);
v___x_4426_ = l_Lean_Expr_letE___override(v_declName_4405_, v___x_4422_, v___x_4424_, v_body_4406_, v_nondep_4407_);
v___x_4427_ = lean_apply_8(v___f_4408_, v_fvarIds_4413_, v_givenNames_x27_4415_, v___x_4426_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, lean_box(0));
return v___x_4427_;
}
v___jp_4428_:
{
if (v___y_4429_ == 0)
{
lean_dec(v_mvarId_4411_);
lean_dec(v___x_4410_);
goto v___jp_4425_;
}
else
{
uint8_t v___x_4430_; 
v___x_4430_ = lean_expr_eqv(v_value_4409_, v___x_4424_);
if (v___x_4430_ == 0)
{
lean_dec(v_mvarId_4411_);
lean_dec(v___x_4410_);
goto v___jp_4425_;
}
else
{
lean_object* v___x_4431_; 
v___x_4431_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4410_, v_mvarId_4411_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_dec_ref(v___x_4431_);
goto v___jp_4425_;
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v_givenNames_x27_4415_);
lean_dec_ref(v_fvarIds_4413_);
lean_dec_ref(v___f_4408_);
lean_dec_ref(v_body_4406_);
lean_dec(v_declName_4405_);
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4431_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(lean_object** _args){
lean_object* v___x_4443_ = _args[0];
lean_object* v_declName_4444_ = _args[1];
lean_object* v_body_4445_ = _args[2];
lean_object* v_nondep_4446_ = _args[3];
lean_object* v___f_4447_ = _args[4];
lean_object* v_value_4448_ = _args[5];
lean_object* v___x_4449_ = _args[6];
lean_object* v_mvarId_4450_ = _args[7];
lean_object* v_type_4451_ = _args[8];
lean_object* v_fvarIds_4452_ = _args[9];
lean_object* v_es_4453_ = _args[10];
lean_object* v_givenNames_x27_4454_ = _args[11];
lean_object* v___y_4455_ = _args[12];
lean_object* v___y_4456_ = _args[13];
lean_object* v___y_4457_ = _args[14];
lean_object* v___y_4458_ = _args[15];
lean_object* v___y_4459_ = _args[16];
_start:
{
uint8_t v_nondep_1962__boxed_4460_; lean_object* v_res_4461_; 
v_nondep_1962__boxed_4460_ = lean_unbox(v_nondep_4446_);
v_res_4461_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(v___x_4443_, v_declName_4444_, v_body_4445_, v_nondep_1962__boxed_4460_, v___f_4447_, v_value_4448_, v___x_4449_, v_mvarId_4450_, v_type_4451_, v_fvarIds_4452_, v_es_4453_, v_givenNames_x27_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec_ref(v_es_4453_);
lean_dec_ref(v_type_4451_);
lean_dec_ref(v_value_4448_);
return v_res_4461_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = ((lean_object*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1));
v___x_4466_ = l_Lean_MessageData_ofFormat(v___x_4465_);
return v___x_4466_;
}
}
static lean_object* _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2);
v___x_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3(lean_object* v_mvarId_4469_, lean_object* v___x_4470_, lean_object* v___f_4471_, lean_object* v___x_4472_, lean_object* v_givenNames_4473_, lean_object* v_config_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___x_4480_; 
lean_inc(v_mvarId_4469_);
v___x_4480_ = l_Lean_MVarId_getType(v_mvarId_4469_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref(v___x_4480_);
switch(lean_obj_tag(v_a_4481_))
{
case 7:
{
lean_object* v_binderName_4482_; lean_object* v_binderType_4483_; lean_object* v_body_4484_; uint8_t v_binderInfo_4485_; lean_object* v___x_4486_; lean_object* v___f_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v_binderName_4482_ = lean_ctor_get(v_a_4481_, 0);
lean_inc(v_binderName_4482_);
v_binderType_4483_ = lean_ctor_get(v_a_4481_, 1);
lean_inc_ref(v_binderType_4483_);
v_body_4484_ = lean_ctor_get(v_a_4481_, 2);
lean_inc_ref(v_body_4484_);
v_binderInfo_4485_ = lean_ctor_get_uint8(v_a_4481_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4481_);
v___x_4486_ = lean_box(v_binderInfo_4485_);
lean_inc_ref(v_binderType_4483_);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4487_, 0, v___x_4470_);
lean_closure_set(v___f_4487_, 1, v_binderName_4482_);
lean_closure_set(v___f_4487_, 2, v_body_4484_);
lean_closure_set(v___f_4487_, 3, v___x_4486_);
lean_closure_set(v___f_4487_, 4, v___f_4471_);
lean_closure_set(v___f_4487_, 5, v___x_4472_);
lean_closure_set(v___f_4487_, 6, v_mvarId_4469_);
lean_closure_set(v___f_4487_, 7, v_binderType_4483_);
v___x_4488_ = lean_unsigned_to_nat(1u);
v___x_4489_ = lean_mk_empty_array_with_capacity(v___x_4488_);
v___x_4490_ = lean_array_push(v___x_4489_, v_binderType_4483_);
v___x_4491_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4490_, v_givenNames_4473_, v___f_4487_, v_config_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4491_;
}
case 8:
{
lean_object* v_declName_4492_; lean_object* v_type_4493_; lean_object* v_value_4494_; lean_object* v_body_4495_; uint8_t v_nondep_4496_; lean_object* v___x_4497_; lean_object* v___f_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v_declName_4492_ = lean_ctor_get(v_a_4481_, 0);
lean_inc(v_declName_4492_);
v_type_4493_ = lean_ctor_get(v_a_4481_, 1);
lean_inc_ref(v_type_4493_);
v_value_4494_ = lean_ctor_get(v_a_4481_, 2);
lean_inc_ref(v_value_4494_);
v_body_4495_ = lean_ctor_get(v_a_4481_, 3);
lean_inc_ref(v_body_4495_);
v_nondep_4496_ = lean_ctor_get_uint8(v_a_4481_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4481_);
v___x_4497_ = lean_box(v_nondep_4496_);
lean_inc_ref(v_type_4493_);
lean_inc_ref(v_value_4494_);
v___f_4498_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed), 17, 9);
lean_closure_set(v___f_4498_, 0, v___x_4470_);
lean_closure_set(v___f_4498_, 1, v_declName_4492_);
lean_closure_set(v___f_4498_, 2, v_body_4495_);
lean_closure_set(v___f_4498_, 3, v___x_4497_);
lean_closure_set(v___f_4498_, 4, v___f_4471_);
lean_closure_set(v___f_4498_, 5, v_value_4494_);
lean_closure_set(v___f_4498_, 6, v___x_4472_);
lean_closure_set(v___f_4498_, 7, v_mvarId_4469_);
lean_closure_set(v___f_4498_, 8, v_type_4493_);
v___x_4499_ = lean_unsigned_to_nat(2u);
v___x_4500_ = lean_mk_empty_array_with_capacity(v___x_4499_);
v___x_4501_ = lean_array_push(v___x_4500_, v_type_4493_);
v___x_4502_ = lean_array_push(v___x_4501_, v_value_4494_);
v___x_4503_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_4502_, v_givenNames_4473_, v___f_4498_, v_config_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4503_;
}
default: 
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
lean_dec(v_a_4481_);
lean_dec_ref(v_config_4474_);
lean_dec(v_givenNames_4473_);
lean_dec_ref(v___f_4471_);
lean_dec_ref(v___x_4470_);
v___x_4504_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4505_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4472_, v_mvarId_4469_, v___x_4504_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
return v___x_4505_;
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec_ref(v_config_4474_);
lean_dec(v_givenNames_4473_);
lean_dec(v___x_4472_);
lean_dec_ref(v___f_4471_);
lean_dec_ref(v___x_4470_);
lean_dec(v_mvarId_4469_);
v_a_4506_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4480_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4480_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(lean_object* v_mvarId_4514_, lean_object* v___x_4515_, lean_object* v___f_4516_, lean_object* v___x_4517_, lean_object* v_givenNames_4518_, lean_object* v_config_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(v_mvarId_4514_, v___x_4515_, v___f_4516_, v___x_4517_, v_givenNames_4518_, v_config_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4(lean_object* v___x_4526_, lean_object* v___x_4527_, lean_object* v_givenNames_4528_, lean_object* v_config_4529_, lean_object* v_mvarId_4530_, lean_object* v_fvars_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v___f_4537_; lean_object* v___f_4538_; lean_object* v___x_4539_; 
lean_inc(v_mvarId_4530_);
v___f_4537_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4537_, 0, v_mvarId_4530_);
lean_closure_set(v___f_4537_, 1, v_fvars_4531_);
lean_inc(v_mvarId_4530_);
v___f_4538_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed), 11, 6);
lean_closure_set(v___f_4538_, 0, v_mvarId_4530_);
lean_closure_set(v___f_4538_, 1, v___x_4526_);
lean_closure_set(v___f_4538_, 2, v___f_4537_);
lean_closure_set(v___f_4538_, 3, v___x_4527_);
lean_closure_set(v___f_4538_, 4, v_givenNames_4528_);
lean_closure_set(v___f_4538_, 5, v_config_4529_);
v___x_4539_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4530_, v___f_4538_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(lean_object* v___x_4540_, lean_object* v___x_4541_, lean_object* v_givenNames_4542_, lean_object* v_config_4543_, lean_object* v_mvarId_4544_, lean_object* v_fvars_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(v___x_4540_, v___x_4541_, v_givenNames_4542_, v_config_4543_, v_mvarId_4544_, v_fvars_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object* v_mvarId_4552_, lean_object* v_fvarId_4553_, lean_object* v_givenNames_4554_, lean_object* v_config_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4561_ = ((lean_object*)(l_Lean_MVarId_extractLets___closed__1));
lean_inc(v_mvarId_4552_);
v___x_4562_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4552_, v___x_4561_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v___x_4563_; lean_object* v___f_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; lean_object* v___x_4569_; 
lean_dec_ref(v___x_4562_);
v___x_4563_ = l_Lean_instInhabitedExpr;
v___f_4564_ = lean_alloc_closure((void*)(l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed), 11, 4);
lean_closure_set(v___f_4564_, 0, v___x_4563_);
lean_closure_set(v___f_4564_, 1, v___x_4561_);
lean_closure_set(v___f_4564_, 2, v_givenNames_4554_);
lean_closure_set(v___f_4564_, 3, v_config_4555_);
v___x_4565_ = lean_unsigned_to_nat(1u);
v___x_4566_ = lean_mk_empty_array_with_capacity(v___x_4565_);
v___x_4567_ = lean_array_push(v___x_4566_, v_fvarId_4553_);
v___x_4568_ = 0;
v___x_4569_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4552_, v___x_4567_, v___f_4564_, v___x_4568_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
return v___x_4569_;
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec_ref(v_config_4555_);
lean_dec(v_givenNames_4554_);
lean_dec(v_fvarId_4553_);
lean_dec(v_mvarId_4552_);
v_a_4570_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4562_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4562_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_extractLetsLocalDecl___boxed(lean_object* v_mvarId_4578_, lean_object* v_fvarId_4579_, lean_object* v_givenNames_4580_, lean_object* v_config_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_MVarId_extractLetsLocalDecl(v_mvarId_4578_, v_fvarId_4579_, v_givenNames_4580_, v_config_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0(lean_object* v_mvarId_4588_, lean_object* v___x_4589_, lean_object* v_config_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v___x_4596_; 
lean_inc(v___x_4589_);
lean_inc(v_mvarId_4588_);
v___x_4596_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4588_, v___x_4589_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v___x_4597_; 
lean_dec_ref(v___x_4596_);
lean_inc(v_mvarId_4588_);
v___x_4597_ = l_Lean_MVarId_getType(v_mvarId_4588_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4599_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
lean_inc(v___y_4594_);
lean_inc_ref(v___y_4593_);
lean_inc(v___y_4592_);
lean_inc_ref(v___y_4591_);
lean_inc(v_a_4598_);
v___x_4599_ = l_Lean_Meta_liftLets(v_a_4598_, v_config_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; uint8_t v___x_4601_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = lean_expr_eqv(v_a_4598_, v_a_4600_);
lean_dec(v_a_4598_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; 
lean_dec(v___x_4589_);
v___x_4602_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4588_, v_a_4600_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
return v___x_4602_;
}
else
{
lean_object* v___x_4603_; 
lean_inc(v_mvarId_4588_);
v___x_4603_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4589_, v_mvarId_4588_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v___x_4604_; 
lean_dec_ref(v___x_4603_);
v___x_4604_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4588_, v_a_4600_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
return v___x_4604_;
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec(v_a_4600_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v_mvarId_4588_);
v_a_4605_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4603_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4603_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
lean_dec(v_a_4598_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___x_4589_);
lean_dec(v_mvarId_4588_);
v_a_4613_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4599_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4599_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec_ref(v_config_4590_);
lean_dec(v___x_4589_);
lean_dec(v_mvarId_4588_);
v_a_4621_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4597_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4597_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec_ref(v_config_4590_);
lean_dec(v___x_4589_);
lean_dec(v_mvarId_4588_);
v_a_4629_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4596_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4596_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___lam__0___boxed(lean_object* v_mvarId_4637_, lean_object* v___x_4638_, lean_object* v_config_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_Lean_MVarId_liftLets___lam__0(v_mvarId_4637_, v___x_4638_, v_config_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets(lean_object* v_mvarId_4649_, lean_object* v_config_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
lean_object* v___x_4656_; lean_object* v___f_4657_; lean_object* v___x_4658_; 
v___x_4656_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4649_);
v___f_4657_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLets___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4657_, 0, v_mvarId_4649_);
lean_closure_set(v___f_4657_, 1, v___x_4656_);
lean_closure_set(v___f_4657_, 2, v_config_4650_);
v___x_4658_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4649_, v___f_4657_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLets___boxed(lean_object* v_mvarId_4659_, lean_object* v_config_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_Lean_MVarId_liftLets(v_mvarId_4659_, v_config_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0(lean_object* v_mvarId_4667_, lean_object* v_fvars_4668_, lean_object* v_targetNew_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4667_, v_targetNew_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4689_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4689_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4689_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; size_t v_sz_4681_; size_t v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4680_ = lean_box(0);
v_sz_4681_ = lean_array_size(v_fvars_4668_);
v___x_4682_ = ((size_t)0ULL);
v___x_4683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_4681_, v___x_4682_, v_fvars_4668_);
v___x_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
lean_ctor_set(v___x_4684_, 1, v_a_4676_);
v___x_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4680_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v___x_4685_);
v___x_4687_ = v___x_4678_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
lean_dec_ref(v_fvars_4668_);
v_a_4690_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4675_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4675_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(lean_object* v_mvarId_4698_, lean_object* v_fvars_4699_, lean_object* v_targetNew_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(v_mvarId_4698_, v_fvars_4699_, v_targetNew_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1(lean_object* v_mvarId_4707_, lean_object* v_config_4708_, lean_object* v___f_4709_, lean_object* v___x_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v___x_4716_; 
lean_inc(v_mvarId_4707_);
v___x_4716_ = l_Lean_MVarId_getType(v_mvarId_4707_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref(v___x_4716_);
switch(lean_obj_tag(v_a_4717_))
{
case 7:
{
lean_object* v_binderName_4718_; lean_object* v_binderType_4719_; lean_object* v_body_4720_; uint8_t v_binderInfo_4721_; lean_object* v___x_4722_; 
v_binderName_4718_ = lean_ctor_get(v_a_4717_, 0);
lean_inc(v_binderName_4718_);
v_binderType_4719_ = lean_ctor_get(v_a_4717_, 1);
lean_inc_ref(v_binderType_4719_);
v_body_4720_ = lean_ctor_get(v_a_4717_, 2);
lean_inc_ref(v_body_4720_);
v_binderInfo_4721_ = lean_ctor_get_uint8(v_a_4717_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_4717_);
lean_inc(v___y_4714_);
lean_inc_ref(v___y_4713_);
lean_inc(v___y_4712_);
lean_inc_ref(v___y_4711_);
lean_inc_ref(v_binderType_4719_);
v___x_4722_ = l_Lean_Meta_liftLets(v_binderType_4719_, v_config_4708_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; uint8_t v___x_4731_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref(v___x_4722_);
v___x_4731_ = lean_expr_eqv(v_binderType_4719_, v_a_4723_);
lean_dec_ref(v_binderType_4719_);
if (v___x_4731_ == 0)
{
lean_dec(v___x_4710_);
lean_dec(v_mvarId_4707_);
v___y_4725_ = v___y_4711_;
v___y_4726_ = v___y_4712_;
v___y_4727_ = v___y_4713_;
v___y_4728_ = v___y_4714_;
goto v___jp_4724_;
}
else
{
lean_object* v___x_4732_; 
v___x_4732_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4710_, v_mvarId_4707_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_dec_ref(v___x_4732_);
v___y_4725_ = v___y_4711_;
v___y_4726_ = v___y_4712_;
v___y_4727_ = v___y_4713_;
v___y_4728_ = v___y_4714_;
goto v___jp_4724_;
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec(v_a_4723_);
lean_dec_ref(v_body_4720_);
lean_dec(v_binderName_4718_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec_ref(v___f_4709_);
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4732_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4732_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
v___jp_4724_:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4729_ = l_Lean_Expr_forallE___override(v_binderName_4718_, v_a_4723_, v_body_4720_, v_binderInfo_4721_);
v___x_4730_ = lean_apply_6(v___f_4709_, v___x_4729_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, lean_box(0));
return v___x_4730_;
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
lean_dec_ref(v_body_4720_);
lean_dec_ref(v_binderType_4719_);
lean_dec(v_binderName_4718_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4710_);
lean_dec_ref(v___f_4709_);
lean_dec(v_mvarId_4707_);
v_a_4741_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4722_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4722_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
case 8:
{
lean_object* v_declName_4749_; lean_object* v_type_4750_; lean_object* v_value_4751_; lean_object* v_body_4752_; uint8_t v_nondep_4753_; lean_object* v___x_4754_; 
v_declName_4749_ = lean_ctor_get(v_a_4717_, 0);
lean_inc(v_declName_4749_);
v_type_4750_ = lean_ctor_get(v_a_4717_, 1);
lean_inc_ref(v_type_4750_);
v_value_4751_ = lean_ctor_get(v_a_4717_, 2);
lean_inc_ref(v_value_4751_);
v_body_4752_ = lean_ctor_get(v_a_4717_, 3);
lean_inc_ref(v_body_4752_);
v_nondep_4753_ = lean_ctor_get_uint8(v_a_4717_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_4717_);
lean_inc(v___y_4714_);
lean_inc_ref(v___y_4713_);
lean_inc(v___y_4712_);
lean_inc_ref(v___y_4711_);
lean_inc_ref(v_config_4708_);
lean_inc_ref(v_type_4750_);
v___x_4754_ = l_Lean_Meta_liftLets(v_type_4750_, v_config_4708_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4756_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_a_4755_);
lean_dec_ref(v___x_4754_);
lean_inc(v___y_4714_);
lean_inc_ref(v___y_4713_);
lean_inc(v___y_4712_);
lean_inc_ref(v___y_4711_);
lean_inc_ref(v_value_4751_);
v___x_4756_ = l_Lean_Meta_liftLets(v_value_4751_, v_config_4708_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4761_; lean_object* v___y_4762_; uint8_t v___y_4766_; uint8_t v___x_4776_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref(v___x_4756_);
v___x_4776_ = lean_expr_eqv(v_type_4750_, v_a_4755_);
lean_dec_ref(v_type_4750_);
if (v___x_4776_ == 0)
{
lean_dec_ref(v_value_4751_);
v___y_4766_ = v___x_4776_;
goto v___jp_4765_;
}
else
{
uint8_t v___x_4777_; 
v___x_4777_ = lean_expr_eqv(v_value_4751_, v_a_4757_);
lean_dec_ref(v_value_4751_);
v___y_4766_ = v___x_4777_;
goto v___jp_4765_;
}
v___jp_4758_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = l_Lean_Expr_letE___override(v_declName_4749_, v_a_4755_, v_a_4757_, v_body_4752_, v_nondep_4753_);
v___x_4764_ = lean_apply_6(v___f_4709_, v___x_4763_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, lean_box(0));
return v___x_4764_;
}
v___jp_4765_:
{
if (v___y_4766_ == 0)
{
lean_dec(v___x_4710_);
lean_dec(v_mvarId_4707_);
v___y_4759_ = v___y_4711_;
v___y_4760_ = v___y_4712_;
v___y_4761_ = v___y_4713_;
v___y_4762_ = v___y_4714_;
goto v___jp_4758_;
}
else
{
lean_object* v___x_4767_; 
v___x_4767_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4710_, v_mvarId_4707_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
if (lean_obj_tag(v___x_4767_) == 0)
{
lean_dec_ref(v___x_4767_);
v___y_4759_ = v___y_4711_;
v___y_4760_ = v___y_4712_;
v___y_4761_ = v___y_4713_;
v___y_4762_ = v___y_4714_;
goto v___jp_4758_;
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
lean_dec(v_a_4757_);
lean_dec(v_a_4755_);
lean_dec_ref(v_body_4752_);
lean_dec(v_declName_4749_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec_ref(v___f_4709_);
v_a_4768_ = lean_ctor_get(v___x_4767_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4767_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4767_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4767_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_dec(v_a_4755_);
lean_dec_ref(v_body_4752_);
lean_dec_ref(v_value_4751_);
lean_dec_ref(v_type_4750_);
lean_dec(v_declName_4749_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4710_);
lean_dec_ref(v___f_4709_);
lean_dec(v_mvarId_4707_);
v_a_4778_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4756_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4756_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec_ref(v_body_4752_);
lean_dec_ref(v_value_4751_);
lean_dec_ref(v_type_4750_);
lean_dec(v_declName_4749_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4710_);
lean_dec_ref(v___f_4709_);
lean_dec_ref(v_config_4708_);
lean_dec(v_mvarId_4707_);
v_a_4786_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4754_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4754_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
default: 
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
lean_dec(v_a_4717_);
lean_dec_ref(v___f_4709_);
lean_dec_ref(v_config_4708_);
v___x_4794_ = lean_obj_once(&l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3, &l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once, _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3);
v___x_4795_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4710_, v_mvarId_4707_, v___x_4794_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
return v___x_4795_;
}
}
}
else
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4803_; 
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___x_4710_);
lean_dec_ref(v___f_4709_);
lean_dec_ref(v_config_4708_);
lean_dec(v_mvarId_4707_);
v_a_4796_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4798_ = v___x_4716_;
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4716_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4796_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(lean_object* v_mvarId_4804_, lean_object* v_config_4805_, lean_object* v___f_4806_, lean_object* v___x_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(v_mvarId_4804_, v_config_4805_, v___f_4806_, v___x_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2(lean_object* v_config_4814_, lean_object* v___x_4815_, lean_object* v_mvarId_4816_, lean_object* v_fvars_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___f_4823_; lean_object* v___f_4824_; lean_object* v___x_4825_; 
lean_inc(v_mvarId_4816_);
v___f_4823_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4823_, 0, v_mvarId_4816_);
lean_closure_set(v___f_4823_, 1, v_fvars_4817_);
lean_inc(v_mvarId_4816_);
v___f_4824_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4824_, 0, v_mvarId_4816_);
lean_closure_set(v___f_4824_, 1, v_config_4814_);
lean_closure_set(v___f_4824_, 2, v___f_4823_);
lean_closure_set(v___f_4824_, 3, v___x_4815_);
v___x_4825_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4816_, v___f_4824_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(lean_object* v_config_4826_, lean_object* v___x_4827_, lean_object* v_mvarId_4828_, lean_object* v_fvars_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v_res_4835_; 
v_res_4835_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(v_config_4826_, v___x_4827_, v_mvarId_4828_, v_fvars_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object* v_mvarId_4836_, lean_object* v_fvarId_4837_, lean_object* v_config_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = ((lean_object*)(l_Lean_MVarId_liftLets___closed__1));
lean_inc(v_mvarId_4836_);
v___x_4845_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4836_, v___x_4844_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v___f_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; lean_object* v___x_4851_; 
lean_dec_ref(v___x_4845_);
v___f_4846_ = lean_alloc_closure((void*)(l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4846_, 0, v_config_4838_);
lean_closure_set(v___f_4846_, 1, v___x_4844_);
v___x_4847_ = lean_unsigned_to_nat(1u);
v___x_4848_ = lean_mk_empty_array_with_capacity(v___x_4847_);
v___x_4849_ = lean_array_push(v___x_4848_, v_fvarId_4837_);
v___x_4850_ = 0;
v___x_4851_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_4836_, v___x_4849_, v___f_4846_, v___x_4850_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4860_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4860_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4860_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v_snd_4856_; lean_object* v___x_4858_; 
v_snd_4856_ = lean_ctor_get(v_a_4852_, 1);
lean_inc(v_snd_4856_);
lean_dec(v_a_4852_);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v_snd_4856_);
v___x_4858_ = v___x_4854_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_snd_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
v_a_4861_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4851_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4851_);
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
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec_ref(v_config_4838_);
lean_dec(v_fvarId_4837_);
lean_dec(v_mvarId_4836_);
v_a_4869_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4845_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4845_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_liftLetsLocalDecl___boxed(lean_object* v_mvarId_4877_, lean_object* v_fvarId_4878_, lean_object* v_config_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_MVarId_liftLetsLocalDecl(v_mvarId_4877_, v_fvarId_4878_, v_config_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0(lean_object* v_mvarId_4886_, lean_object* v___x_4887_, uint8_t v_failIfUnchanged_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_){
_start:
{
lean_object* v___x_4894_; 
lean_inc(v___x_4887_);
lean_inc(v_mvarId_4886_);
v___x_4894_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4886_, v___x_4887_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v___x_4895_; 
lean_dec_ref(v___x_4894_);
lean_inc(v_mvarId_4886_);
v___x_4895_ = l_Lean_MVarId_getType(v_mvarId_4886_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4897_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref(v___x_4895_);
lean_inc(v___y_4892_);
lean_inc_ref(v___y_4891_);
lean_inc(v___y_4890_);
lean_inc_ref(v___y_4889_);
lean_inc(v_a_4896_);
v___x_4897_ = l_Lean_Meta_letToHave(v_a_4896_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
if (lean_obj_tag(v___x_4897_) == 0)
{
if (v_failIfUnchanged_4888_ == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4899_; 
lean_dec(v_a_4896_);
lean_dec(v___x_4887_);
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref(v___x_4897_);
v___x_4899_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4886_, v_a_4898_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
return v___x_4899_;
}
else
{
lean_object* v_a_4900_; uint8_t v___x_4901_; 
v_a_4900_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4900_);
lean_dec_ref(v___x_4897_);
v___x_4901_ = lean_expr_eqv(v_a_4896_, v_a_4900_);
lean_dec(v_a_4896_);
if (v___x_4901_ == 0)
{
lean_object* v___x_4902_; 
lean_dec(v___x_4887_);
v___x_4902_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4886_, v_a_4900_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
return v___x_4902_;
}
else
{
lean_object* v___x_4903_; 
lean_inc(v_mvarId_4886_);
v___x_4903_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4887_, v_mvarId_4886_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v___x_4904_; 
lean_dec_ref(v___x_4903_);
v___x_4904_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_4886_, v_a_4900_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
return v___x_4904_;
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_dec(v_a_4900_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v_mvarId_4886_);
v_a_4905_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4903_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4903_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec(v_a_4896_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v___x_4887_);
lean_dec(v_mvarId_4886_);
v_a_4913_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4897_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4897_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v___x_4887_);
lean_dec(v_mvarId_4886_);
v_a_4921_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4895_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4895_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
else
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v___x_4887_);
lean_dec(v_mvarId_4886_);
v_a_4929_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4931_ = v___x_4894_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4894_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___lam__0___boxed(lean_object* v_mvarId_4937_, lean_object* v___x_4938_, lean_object* v_failIfUnchanged_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4945_; lean_object* v_res_4946_; 
v_failIfUnchanged_boxed_4945_ = lean_unbox(v_failIfUnchanged_4939_);
v_res_4946_ = l_Lean_MVarId_letToHave___lam__0(v_mvarId_4937_, v___x_4938_, v_failIfUnchanged_boxed_4945_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave(lean_object* v_mvarId_4950_, uint8_t v_failIfUnchanged_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___f_4959_; lean_object* v___x_4960_; 
v___x_4957_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_4958_ = lean_box(v_failIfUnchanged_4951_);
lean_inc(v_mvarId_4950_);
v___f_4959_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHave___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4959_, 0, v_mvarId_4950_);
lean_closure_set(v___f_4959_, 1, v___x_4957_);
lean_closure_set(v___f_4959_, 2, v___x_4958_);
v___x_4960_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_4950_, v___f_4959_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHave___boxed(lean_object* v_mvarId_4961_, lean_object* v_failIfUnchanged_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
uint8_t v_failIfUnchanged_boxed_4968_; lean_object* v_res_4969_; 
v_failIfUnchanged_boxed_4968_ = lean_unbox(v_failIfUnchanged_4962_);
v_res_4969_ = l_Lean_MVarId_letToHave(v_mvarId_4961_, v_failIfUnchanged_boxed_4968_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0(lean_object* v_mvarId_4970_, lean_object* v___x_4971_, lean_object* v_fvarId_4972_, uint8_t v_failIfUnchanged_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v___x_4979_; 
lean_inc(v___x_4971_);
lean_inc(v_mvarId_4970_);
v___x_4979_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4970_, v___x_4971_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v___x_4980_; 
lean_dec_ref(v___x_4979_);
lean_inc_ref(v___y_4974_);
lean_inc(v_fvarId_4972_);
v___x_4980_ = l_Lean_FVarId_getType___redArg(v_fvarId_4972_, v___y_4974_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4982_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4981_);
lean_dec_ref(v___x_4980_);
lean_inc(v___y_4977_);
lean_inc_ref(v___y_4976_);
lean_inc(v___y_4975_);
lean_inc_ref(v___y_4974_);
lean_inc(v_a_4981_);
v___x_4982_ = l_Lean_Meta_letToHave(v_a_4981_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4982_) == 0)
{
if (v_failIfUnchanged_4973_ == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4984_; 
lean_dec(v_a_4981_);
lean_dec(v___x_4971_);
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref(v___x_4982_);
v___x_4984_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4970_, v_fvarId_4972_, v_a_4983_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_4984_;
}
else
{
lean_object* v_a_4985_; uint8_t v___x_4986_; 
v_a_4985_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4985_);
lean_dec_ref(v___x_4982_);
v___x_4986_ = lean_expr_eqv(v_a_4981_, v_a_4985_);
lean_dec(v_a_4981_);
if (v___x_4986_ == 0)
{
lean_object* v___x_4987_; 
lean_dec(v___x_4971_);
v___x_4987_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4970_, v_fvarId_4972_, v_a_4985_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_4987_;
}
else
{
lean_object* v___x_4988_; 
lean_inc(v_mvarId_4970_);
v___x_4988_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_4971_, v_mvarId_4970_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v___x_4989_; 
lean_dec_ref(v___x_4988_);
v___x_4989_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_4970_, v_fvarId_4972_, v_a_4985_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_4989_;
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_dec(v_a_4985_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v_fvarId_4972_);
lean_dec(v_mvarId_4970_);
v_a_4990_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4988_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4988_);
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
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec(v_a_4981_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v_fvarId_4972_);
lean_dec(v___x_4971_);
lean_dec(v_mvarId_4970_);
v_a_4998_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4982_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4982_);
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
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v_fvarId_4972_);
lean_dec(v___x_4971_);
lean_dec(v_mvarId_4970_);
v_a_5006_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4980_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4980_);
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
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v_fvarId_4972_);
lean_dec(v___x_4971_);
lean_dec(v_mvarId_4970_);
v_a_5014_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_4979_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_4979_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(lean_object* v_mvarId_5022_, lean_object* v___x_5023_, lean_object* v_fvarId_5024_, lean_object* v_failIfUnchanged_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5031_; lean_object* v_res_5032_; 
v_failIfUnchanged_boxed_5031_ = lean_unbox(v_failIfUnchanged_5025_);
v_res_5032_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(v_mvarId_5022_, v___x_5023_, v_fvarId_5024_, v_failIfUnchanged_boxed_5031_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object* v_mvarId_5033_, lean_object* v_fvarId_5034_, uint8_t v_failIfUnchanged_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___f_5043_; lean_object* v___x_5044_; 
v___x_5041_ = ((lean_object*)(l_Lean_MVarId_letToHave___closed__1));
v___x_5042_ = lean_box(v_failIfUnchanged_5035_);
lean_inc(v_mvarId_5033_);
v___f_5043_ = lean_alloc_closure((void*)(l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_5043_, 0, v_mvarId_5033_);
lean_closure_set(v___f_5043_, 1, v___x_5041_);
lean_closure_set(v___f_5043_, 2, v_fvarId_5034_);
lean_closure_set(v___f_5043_, 3, v___x_5042_);
v___x_5044_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(v_mvarId_5033_, v___f_5043_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_letToHaveLocalDecl___boxed(lean_object* v_mvarId_5045_, lean_object* v_fvarId_5046_, lean_object* v_failIfUnchanged_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_){
_start:
{
uint8_t v_failIfUnchanged_boxed_5053_; lean_object* v_res_5054_; 
v_failIfUnchanged_boxed_5053_ = lean_unbox(v_failIfUnchanged_5047_);
v_res_5054_ = l_Lean_MVarId_letToHaveLocalDecl(v_mvarId_5045_, v_fvarId_5046_, v_failIfUnchanged_boxed_5053_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
return v_res_5054_;
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
