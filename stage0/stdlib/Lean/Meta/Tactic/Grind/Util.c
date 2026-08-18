// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Util
// Imports: public import Lean.Meta.Tactic.Simp.Simproc import Init.Simproc import Lean.Meta.Tactic.Clear import Lean.Meta.Sym.Util public import Init.Grind.Config import Init.Grind.Util import Lean.Structure
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
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalContext_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_ensureNoMVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_MVarId_ensureNoMVar___closed__0 = (const lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_ensureNoMVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_MVarId_ensureNoMVar___closed__1 = (const lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__1_value;
static const lean_string_object l_Lean_MVarId_ensureNoMVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "goal contains metavariables"};
static const lean_object* l_Lean_MVarId_ensureNoMVar___closed__2 = (const lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_ensureNoMVar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__2_value)}};
static const lean_object* l_Lean_MVarId_ensureNoMVar___closed__3 = (const lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_ensureNoMVar___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__4;
static lean_once_cell_t l_Lean_MVarId_ensureNoMVar___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_ensureNoMVar___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.MetavarContext"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.instantiateLCtxMVars"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Invalid auxiliary declaration found in local context: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = " does not have an associated full name."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3;
static lean_once_cell_t l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_unfoldReducible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducible___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_unfoldReducible___closed__0 = (const lean_object*)&l_Lean_MVarId_unfoldReducible___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_betaReduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_betaReduce___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_betaReduce___closed__0 = (const lean_object*)&l_Lean_MVarId_betaReduce___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_byContra_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__2;
static const lean_string_object l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value;
static const lean_string_object l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "byContradiction"};
static const lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 54, 188, 55, 95, 58, 91, 50)}};
static const lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__5 = (const lean_object*)&l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byContra_x3f___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_byContra_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "by_contra"};
static const lean_object* l_Lean_MVarId_byContra_x3f___closed__0 = (const lean_object*)&l_Lean_MVarId_byContra_x3f___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_byContra_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_MVarId_byContra_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_byContra_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_MVarId_byContra_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 137, 84, 152, 220, 16, 123, 158)}};
static const lean_object* l_Lean_MVarId_byContra_x3f___closed__1 = (const lean_object*)&l_Lean_MVarId_byContra_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "the goal mentions the declaration `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "`, which is being defined. To avoid circular reasoning, try rewriting the goal to eliminate `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` before using `grind`."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_clearImplDetails___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "clear_aux_decls"};
static const lean_object* l_Lean_MVarId_clearImplDetails___closed__0 = (const lean_object*)&l_Lean_MVarId_clearImplDetails___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_clearImplDetails___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_MVarId_clearImplDetails___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_clearImplDetails___closed__1_value_aux_0),((lean_object*)&l_Lean_MVarId_clearImplDetails___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 140, 16, 0, 25, 231, 204, 177)}};
static const lean_object* l_Lean_MVarId_clearImplDetails___closed__1 = (const lean_object*)&l_Lean_MVarId_clearImplDetails___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isMData___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_markAsMatchCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_markAsMatchCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_markAsMatchCond___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchCond"};
static const lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_markAsMatchCond___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__2_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 187, 249, 156, 65, 204, 232)}};
static const lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_markAsMatchCond___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_markAsMatchCond___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreMatchCond"};
static const lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 220, 208, 216, 173, 156, 210, 29)}};
static const lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_markAsPreMatchCond___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "reducePreMatchCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(150, 224, 247, 141, 87, 215, 99, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_replacePreMatchCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_isPreMatchCond___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_replacePreMatchCond___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_replacePreMatchCond___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_replacePreMatchCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_replacePreMatchCond___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_replacePreMatchCond___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_replacePreMatchCond___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_replacePreMatchCond___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_replacePreMatchCond___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_isIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Grind_isIte___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_isIte___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_isIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Grind_isIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_isIte___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_isDIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Meta_Grind_isDIte___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_isDIte___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_isDIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isDIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Meta_Grind_isDIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_isDIte___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__4(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__3));
v___x_51_ = l_Lean_MessageData_ofFormat(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__5(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Lean_MVarId_ensureNoMVar___closed__4, &l_Lean_MVarId_ensureNoMVar___closed__4_once, _init_l_Lean_MVarId_ensureNoMVar___closed__4);
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar(lean_object* v_mvarId_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; 
lean_inc(v_mvarId_54_);
v___x_60_ = l_Lean_MVarId_getType(v_mvarId_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_75_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
v___x_62_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_61_, v_a_56_);
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_75_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
uint8_t v___x_67_; 
v___x_67_ = l_Lean_Expr_hasExprMVar(v_a_63_);
lean_dec(v_a_63_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_70_; 
lean_dec(v_mvarId_54_);
v___x_68_ = lean_box(0);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_68_);
v___x_70_ = v___x_65_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_del_object(v___x_65_);
v___x_72_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_73_ = lean_obj_once(&l_Lean_MVarId_ensureNoMVar___closed__5, &l_Lean_MVarId_ensureNoMVar___closed__5_once, _init_l_Lean_MVarId_ensureNoMVar___closed__5);
v___x_74_ = l_Lean_Meta_throwTacticEx___redArg(v___x_72_, v_mvarId_54_, v___x_73_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
return v___x_74_;
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec(v_mvarId_54_);
v_a_76_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_60_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_60_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar___boxed(lean_object* v_mvarId_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_MVarId_ensureNoMVar(v_mvarId_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_90_;
}
}
static lean_object* _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_instMonadEIO(lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_toApplicative_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_165_; 
v___x_102_ = lean_obj_once(&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0, &l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0);
v___x_103_ = l_StateRefT_x27_instMonad___redArg(v___x_102_);
v_toApplicative_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; 
v_unused_166_ = lean_ctor_get(v___x_103_, 1);
lean_dec(v_unused_166_);
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_165_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_toApplicative_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_165_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_toFunctor_108_; lean_object* v_toSeq_109_; lean_object* v_toSeqLeft_110_; lean_object* v_toSeqRight_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_163_; 
v_toFunctor_108_ = lean_ctor_get(v_toApplicative_104_, 0);
v_toSeq_109_ = lean_ctor_get(v_toApplicative_104_, 2);
v_toSeqLeft_110_ = lean_ctor_get(v_toApplicative_104_, 3);
v_toSeqRight_111_ = lean_ctor_get(v_toApplicative_104_, 4);
v_isSharedCheck_163_ = !lean_is_exclusive(v_toApplicative_104_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v_toApplicative_104_, 1);
lean_dec(v_unused_164_);
v___x_113_ = v_toApplicative_104_;
v_isShared_114_ = v_isSharedCheck_163_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_toSeqRight_111_);
lean_inc(v_toSeqLeft_110_);
lean_inc(v_toSeq_109_);
lean_inc(v_toFunctor_108_);
lean_dec(v_toApplicative_104_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_163_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___x_124_; 
v___f_115_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1));
v___f_116_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_108_);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_117_, 0, v_toFunctor_108_);
v___f_118_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_118_, 0, v_toFunctor_108_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___f_117_);
lean_ctor_set(v___x_119_, 1, v___f_118_);
v___f_120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_120_, 0, v_toSeqRight_111_);
v___f_121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_121_, 0, v_toSeqLeft_110_);
v___f_122_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_122_, 0, v_toSeq_109_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v___f_120_);
lean_ctor_set(v___x_113_, 3, v___f_121_);
lean_ctor_set(v___x_113_, 2, v___f_122_);
lean_ctor_set(v___x_113_, 1, v___f_115_);
lean_ctor_set(v___x_113_, 0, v___x_119_);
v___x_124_ = v___x_113_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___f_115_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v___f_122_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v___f_121_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v___f_120_);
v___x_124_ = v_reuseFailAlloc_162_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_126_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___f_116_);
lean_ctor_set(v___x_106_, 0, v___x_124_);
v___x_126_ = v___x_106_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___f_116_);
v___x_126_ = v_reuseFailAlloc_161_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v_toApplicative_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_159_; 
v___x_127_ = l_StateRefT_x27_instMonad___redArg(v___x_126_);
v_toApplicative_128_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v___x_127_, 1);
lean_dec(v_unused_160_);
v___x_130_ = v___x_127_;
v_isShared_131_ = v_isSharedCheck_159_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_toApplicative_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_159_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_toFunctor_132_; lean_object* v_toSeq_133_; lean_object* v_toSeqLeft_134_; lean_object* v_toSeqRight_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_157_; 
v_toFunctor_132_ = lean_ctor_get(v_toApplicative_128_, 0);
v_toSeq_133_ = lean_ctor_get(v_toApplicative_128_, 2);
v_toSeqLeft_134_ = lean_ctor_get(v_toApplicative_128_, 3);
v_toSeqRight_135_ = lean_ctor_get(v_toApplicative_128_, 4);
v_isSharedCheck_157_ = !lean_is_exclusive(v_toApplicative_128_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v_toApplicative_128_, 1);
lean_dec(v_unused_158_);
v___x_137_ = v_toApplicative_128_;
v_isShared_138_ = v_isSharedCheck_157_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_toSeqRight_135_);
lean_inc(v_toSeqLeft_134_);
lean_inc(v_toSeq_133_);
lean_inc(v_toFunctor_132_);
lean_dec(v_toApplicative_128_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_157_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_148_; 
v___f_139_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3));
v___f_140_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_132_);
v___f_141_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_141_, 0, v_toFunctor_132_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_142_, 0, v_toFunctor_132_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___f_141_);
lean_ctor_set(v___x_143_, 1, v___f_142_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_144_, 0, v_toSeqRight_135_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_145_, 0, v_toSeqLeft_134_);
v___f_146_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_146_, 0, v_toSeq_133_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 4, v___f_144_);
lean_ctor_set(v___x_137_, 3, v___f_145_);
lean_ctor_set(v___x_137_, 2, v___f_146_);
lean_ctor_set(v___x_137_, 1, v___f_139_);
lean_ctor_set(v___x_137_, 0, v___x_143_);
v___x_148_ = v___x_137_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___f_139_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v___f_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v___f_145_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v___f_144_);
v___x_148_ = v_reuseFailAlloc_156_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___f_140_);
lean_ctor_set(v___x_130_, 0, v___x_148_);
v___x_150_ = v___x_130_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___f_140_);
v___x_150_ = v_reuseFailAlloc_155_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_1365__overap_153_; lean_object* v___x_154_; 
v___x_151_ = l_Lean_instInhabitedLocalContext_default;
v___x_152_ = l_instInhabitedOfMonad___redArg(v___x_150_, v___x_151_);
v___x_1365__overap_153_ = lean_panic_fn_borrowed(v___x_152_, v_msg_96_);
lean_dec(v___x_152_);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
v___x_154_ = lean_apply_5(v___x_1365__overap_153_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, lean_box(0));
return v___x_154_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___boxed(lean_object* v_msg_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v_msg_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(lean_object* v_t_174_, lean_object* v_k_175_){
_start:
{
if (lean_obj_tag(v_t_174_) == 0)
{
lean_object* v_k_176_; lean_object* v_v_177_; lean_object* v_l_178_; lean_object* v_r_179_; uint8_t v___x_180_; 
v_k_176_ = lean_ctor_get(v_t_174_, 1);
v_v_177_ = lean_ctor_get(v_t_174_, 2);
v_l_178_ = lean_ctor_get(v_t_174_, 3);
v_r_179_ = lean_ctor_get(v_t_174_, 4);
v___x_180_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_175_, v_k_176_);
switch(v___x_180_)
{
case 0:
{
v_t_174_ = v_l_178_;
goto _start;
}
case 1:
{
lean_object* v___x_182_; 
lean_inc(v_v_177_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_v_177_);
return v___x_182_;
}
default: 
{
v_t_174_ = v_r_179_;
goto _start;
}
}
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg___boxed(lean_object* v_t_185_, lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_185_, v_k_186_);
lean_dec(v_k_186_);
lean_dec(v_t_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(lean_object* v_auxDeclToFullName_192_, lean_object* v_as_193_, size_t v_i_194_, size_t v_stop_195_, lean_object* v_b_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_a_203_; uint8_t v___x_207_; 
v___x_207_ = lean_usize_dec_eq(v_i_194_, v_stop_195_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_array_uget_borrowed(v_as_193_, v_i_194_);
if (lean_obj_tag(v___x_208_) == 0)
{
v_a_203_ = v_b_196_;
goto v___jp_202_;
}
else
{
lean_object* v_val_209_; 
v_val_209_ = lean_ctor_get(v___x_208_, 0);
if (lean_obj_tag(v_val_209_) == 0)
{
uint8_t v_kind_210_; 
v_kind_210_ = lean_ctor_get_uint8(v_val_209_, sizeof(void*)*4 + 1);
if (v_kind_210_ == 2)
{
lean_object* v_fvarId_211_; lean_object* v_userName_212_; lean_object* v_type_213_; lean_object* v___x_214_; 
v_fvarId_211_ = lean_ctor_get(v_val_209_, 1);
v_userName_212_ = lean_ctor_get(v_val_209_, 2);
v_type_213_ = lean_ctor_get(v_val_209_, 3);
lean_inc_ref(v_type_213_);
v___x_214_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_213_, v___y_198_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_auxDeclToFullName_192_, v_fvarId_211_);
if (lean_obj_tag(v___x_216_) == 1)
{
lean_object* v_val_217_; lean_object* v___x_218_; 
v_val_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v___x_216_, 1);
lean_inc(v_userName_212_);
lean_inc(v_fvarId_211_);
v___x_218_ = l_Lean_LocalContext_mkAuxDecl(v_b_196_, v_fvarId_211_, v_userName_212_, v_a_215_, v_val_217_);
v_a_203_ = v___x_218_;
goto v___jp_202_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v___x_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_b_196_);
v___x_219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0));
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1));
v___x_221_ = lean_unsigned_to_nat(660u);
v___x_222_ = lean_unsigned_to_nat(12u);
v___x_223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2));
v___x_224_ = 1;
lean_inc(v_userName_212_);
v___x_225_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_212_, v___x_224_);
v___x_226_ = lean_string_append(v___x_223_, v___x_225_);
lean_dec_ref(v___x_225_);
v___x_227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3));
v___x_228_ = lean_string_append(v___x_226_, v___x_227_);
v___x_229_ = l_mkPanicMessageWithDecl(v___x_219_, v___x_220_, v___x_221_, v___x_222_, v___x_228_);
lean_dec_ref(v___x_228_);
v___x_230_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v___x_229_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v_a_203_ = v_a_231_;
goto v___jp_202_;
}
else
{
return v___x_230_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v_b_196_);
v_a_232_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_214_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_214_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_fvarId_240_; lean_object* v_userName_241_; lean_object* v_type_242_; uint8_t v_bi_243_; lean_object* v___x_244_; 
v_fvarId_240_ = lean_ctor_get(v_val_209_, 1);
v_userName_241_ = lean_ctor_get(v_val_209_, 2);
v_type_242_ = lean_ctor_get(v_val_209_, 3);
v_bi_243_ = lean_ctor_get_uint8(v_val_209_, sizeof(void*)*4);
lean_inc_ref(v_type_242_);
v___x_244_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_242_, v___y_198_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
lean_inc(v_userName_241_);
lean_inc(v_fvarId_240_);
v___x_246_ = l_Lean_LocalContext_mkLocalDecl(v_b_196_, v_fvarId_240_, v_userName_241_, v_a_245_, v_bi_243_, v_kind_210_);
v_a_203_ = v___x_246_;
goto v___jp_202_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v_b_196_);
v_a_247_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_244_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
else
{
lean_object* v_fvarId_255_; lean_object* v_userName_256_; lean_object* v_type_257_; lean_object* v_value_258_; uint8_t v_nondep_259_; uint8_t v_kind_260_; lean_object* v___x_261_; 
v_fvarId_255_ = lean_ctor_get(v_val_209_, 1);
v_userName_256_ = lean_ctor_get(v_val_209_, 2);
v_type_257_ = lean_ctor_get(v_val_209_, 3);
v_value_258_ = lean_ctor_get(v_val_209_, 4);
v_nondep_259_ = lean_ctor_get_uint8(v_val_209_, sizeof(void*)*5);
v_kind_260_ = lean_ctor_get_uint8(v_val_209_, sizeof(void*)*5 + 1);
lean_inc_ref(v_type_257_);
v___x_261_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_257_, v___y_198_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
lean_inc_ref(v_value_258_);
v___x_263_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_value_258_, v___y_198_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
lean_inc(v_userName_256_);
lean_inc(v_fvarId_255_);
v___x_265_ = l_Lean_LocalContext_mkLetDecl(v_b_196_, v_fvarId_255_, v_userName_256_, v_a_262_, v_a_264_, v_nondep_259_, v_kind_260_);
v_a_203_ = v___x_265_;
goto v___jp_202_;
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec(v_a_262_);
lean_dec_ref(v_b_196_);
v_a_266_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_263_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_263_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_b_196_);
v_a_274_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_261_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_261_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
else
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v_b_196_);
return v___x_282_;
}
v___jp_202_:
{
size_t v___x_204_; size_t v___x_205_; 
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_add(v_i_194_, v___x_204_);
v_i_194_ = v___x_205_;
v_b_196_ = v_a_203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___boxed(lean_object* v_auxDeclToFullName_283_, lean_object* v_as_284_, lean_object* v_i_285_, lean_object* v_stop_286_, lean_object* v_b_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
size_t v_i_boxed_293_; size_t v_stop_boxed_294_; lean_object* v_res_295_; 
v_i_boxed_293_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_stop_boxed_294_ = lean_unbox_usize(v_stop_286_);
lean_dec(v_stop_286_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_283_, v_as_284_, v_i_boxed_293_, v_stop_boxed_294_, v_b_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec_ref(v_as_284_);
lean_dec(v_auxDeclToFullName_283_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(lean_object* v_auxDeclToFullName_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v_cs_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_324_; 
v_cs_304_ = lean_ctor_get(v_x_297_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_324_ == 0)
{
v___x_306_ = v_x_297_;
v_isShared_307_ = v_isSharedCheck_324_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_cs_304_);
lean_dec(v_x_297_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_324_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_array_get_size(v_cs_304_);
v___x_310_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v_cs_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_x_298_);
v___x_312_ = v___x_306_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_x_298_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
uint8_t v___x_314_; 
v___x_314_ = lean_nat_dec_le(v___x_309_, v___x_309_);
if (v___x_314_ == 0)
{
if (v___x_310_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v_cs_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_x_298_);
v___x_316_ = v___x_306_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_x_298_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
else
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
lean_del_object(v___x_306_);
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_309_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_296_, v_cs_304_, v___x_318_, v___x_319_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec_ref(v_cs_304_);
return v___x_320_;
}
}
else
{
size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
lean_del_object(v___x_306_);
v___x_321_ = ((size_t)0ULL);
v___x_322_ = lean_usize_of_nat(v___x_309_);
v___x_323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_296_, v_cs_304_, v___x_321_, v___x_322_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec_ref(v_cs_304_);
return v___x_323_;
}
}
}
}
else
{
lean_object* v_vs_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_345_; 
v_vs_325_ = lean_ctor_get(v_x_297_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_345_ == 0)
{
v___x_327_ = v_x_297_;
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_vs_325_);
lean_dec(v_x_297_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_array_get_size(v_vs_325_);
v___x_331_ = lean_nat_dec_lt(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_vs_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 0);
lean_ctor_set(v___x_327_, 0, v_x_298_);
v___x_333_ = v___x_327_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_x_298_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
uint8_t v___x_335_; 
v___x_335_ = lean_nat_dec_le(v___x_330_, v___x_330_);
if (v___x_335_ == 0)
{
if (v___x_331_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v_vs_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 0);
lean_ctor_set(v___x_327_, 0, v_x_298_);
v___x_337_ = v___x_327_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_x_298_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; 
lean_del_object(v___x_327_);
v___x_339_ = ((size_t)0ULL);
v___x_340_ = lean_usize_of_nat(v___x_330_);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_296_, v_vs_325_, v___x_339_, v___x_340_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec_ref(v_vs_325_);
return v___x_341_;
}
}
else
{
size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; 
lean_del_object(v___x_327_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = lean_usize_of_nat(v___x_330_);
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_296_, v_vs_325_, v___x_342_, v___x_343_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec_ref(v_vs_325_);
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_346_, lean_object* v_as_347_, size_t v_i_348_, size_t v_stop_349_, lean_object* v_b_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_eq(v_i_348_, v_stop_349_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_array_uget_borrowed(v_as_347_, v_i_348_);
lean_inc(v___x_357_);
v___x_358_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_346_, v___x_357_, v_b_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; size_t v___x_360_; size_t v___x_361_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_348_, v___x_360_);
v_i_348_ = v___x_361_;
v_b_350_ = v_a_359_;
goto _start;
}
else
{
return v___x_358_;
}
}
else
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_b_350_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_364_, lean_object* v_as_365_, lean_object* v_i_366_, lean_object* v_stop_367_, lean_object* v_b_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
size_t v_i_boxed_374_; size_t v_stop_boxed_375_; lean_object* v_res_376_; 
v_i_boxed_374_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_stop_boxed_375_ = lean_unbox_usize(v_stop_367_);
lean_dec(v_stop_367_);
v_res_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_364_, v_as_365_, v_i_boxed_374_, v_stop_boxed_375_, v_b_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec_ref(v_as_365_);
lean_dec(v_auxDeclToFullName_364_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_auxDeclToFullName_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_377_, v_x_378_, v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v_auxDeclToFullName_377_);
return v_res_385_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(lean_object* v_auxDeclToFullName_387_, lean_object* v_x_388_, size_t v_x_389_, size_t v_x_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_object* v_cs_397_; lean_object* v___x_398_; size_t v___x_399_; lean_object* v_j_400_; lean_object* v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v_cs_397_ = lean_ctor_get(v_x_388_, 0);
lean_inc_ref(v_cs_397_);
lean_dec_ref_known(v_x_388_, 1);
v___x_398_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0);
v___x_399_ = lean_usize_shift_right(v_x_389_, v_x_390_);
v_j_400_ = lean_usize_to_nat(v___x_399_);
v___x_401_ = lean_array_get_borrowed(v___x_398_, v_cs_397_, v_j_400_);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_shift_left(v___x_402_, v_x_390_);
v___x_404_ = lean_usize_sub(v___x_403_, v___x_402_);
v___x_405_ = lean_usize_land(v_x_389_, v___x_404_);
v___x_406_ = ((size_t)5ULL);
v___x_407_ = lean_usize_sub(v_x_390_, v___x_406_);
lean_inc(v___x_401_);
v___x_408_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_387_, v___x_401_, v___x_405_, v___x_407_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_j_400_, v___x_410_);
lean_dec(v_j_400_);
v___x_412_ = lean_array_get_size(v_cs_397_);
v___x_413_ = lean_nat_dec_lt(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_dec(v___x_411_);
lean_dec(v_a_409_);
lean_dec_ref(v_cs_397_);
return v___x_408_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_le(v___x_412_, v___x_412_);
if (v___x_414_ == 0)
{
if (v___x_413_ == 0)
{
lean_dec(v___x_411_);
lean_dec(v_a_409_);
lean_dec_ref(v_cs_397_);
return v___x_408_;
}
else
{
size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_415_ = lean_usize_of_nat(v___x_411_);
lean_dec(v___x_411_);
v___x_416_ = lean_usize_of_nat(v___x_412_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_387_, v_cs_397_, v___x_415_, v___x_416_, v_a_409_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec_ref(v_cs_397_);
return v___x_417_;
}
}
else
{
size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_418_ = lean_usize_of_nat(v___x_411_);
lean_dec(v___x_411_);
v___x_419_ = lean_usize_of_nat(v___x_412_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_387_, v_cs_397_, v___x_418_, v___x_419_, v_a_409_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec_ref(v_cs_397_);
return v___x_420_;
}
}
}
else
{
lean_dec(v_j_400_);
lean_dec_ref(v_cs_397_);
return v___x_408_;
}
}
else
{
lean_object* v_vs_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_441_; 
v_vs_421_ = lean_ctor_get(v_x_388_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_388_);
if (v_isSharedCheck_441_ == 0)
{
v___x_423_ = v_x_388_;
v_isShared_424_ = v_isSharedCheck_441_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_vs_421_);
lean_dec(v_x_388_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_441_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_usize_to_nat(v_x_389_);
v___x_426_ = lean_array_get_size(v_vs_421_);
v___x_427_ = lean_nat_dec_lt(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_429_; 
lean_dec(v___x_425_);
lean_dec_ref(v_vs_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 0);
lean_ctor_set(v___x_423_, 0, v_x_391_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_x_391_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
uint8_t v___x_431_; 
v___x_431_ = lean_nat_dec_le(v___x_426_, v___x_426_);
if (v___x_431_ == 0)
{
if (v___x_427_ == 0)
{
lean_object* v___x_433_; 
lean_dec(v___x_425_);
lean_dec_ref(v_vs_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 0);
lean_ctor_set(v___x_423_, 0, v_x_391_);
v___x_433_ = v___x_423_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_x_391_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
lean_del_object(v___x_423_);
v___x_435_ = lean_usize_of_nat(v___x_425_);
lean_dec(v___x_425_);
v___x_436_ = lean_usize_of_nat(v___x_426_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_387_, v_vs_421_, v___x_435_, v___x_436_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec_ref(v_vs_421_);
return v___x_437_;
}
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
lean_del_object(v___x_423_);
v___x_438_ = lean_usize_of_nat(v___x_425_);
lean_dec(v___x_425_);
v___x_439_ = lean_usize_of_nat(v___x_426_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_387_, v_vs_421_, v___x_438_, v___x_439_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec_ref(v_vs_421_);
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
size_t v_x_4512__boxed_452_; size_t v_x_4513__boxed_453_; lean_object* v_res_454_; 
v_x_4512__boxed_452_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_x_4513__boxed_453_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_res_454_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_442_, v_x_443_, v_x_4512__boxed_452_, v_x_4513__boxed_453_, v_x_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v_auxDeclToFullName_442_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(lean_object* v_auxDeclToFullName_455_, lean_object* v_t_456_, lean_object* v_init_457_, lean_object* v_start_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_nat_dec_eq(v_start_458_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v_root_466_; lean_object* v_tail_467_; size_t v_shift_468_; lean_object* v_tailOff_469_; uint8_t v___x_470_; 
v_root_466_ = lean_ctor_get(v_t_456_, 0);
lean_inc_ref(v_root_466_);
v_tail_467_ = lean_ctor_get(v_t_456_, 1);
lean_inc_ref(v_tail_467_);
v_shift_468_ = lean_ctor_get_usize(v_t_456_, 4);
v_tailOff_469_ = lean_ctor_get(v_t_456_, 3);
lean_inc(v_tailOff_469_);
lean_dec_ref(v_t_456_);
v___x_470_ = lean_nat_dec_le(v_tailOff_469_, v_start_458_);
if (v___x_470_ == 0)
{
size_t v___x_471_; lean_object* v___x_472_; 
lean_dec(v_tailOff_469_);
v___x_471_ = lean_usize_of_nat(v_start_458_);
v___x_472_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_455_, v_root_466_, v___x_471_, v_shift_468_, v_init_457_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
v___x_474_ = lean_array_get_size(v_tail_467_);
v___x_475_ = lean_nat_dec_lt(v___x_464_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec(v_a_473_);
lean_dec_ref(v_tail_467_);
return v___x_472_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_le(v___x_474_, v___x_474_);
if (v___x_476_ == 0)
{
if (v___x_475_ == 0)
{
lean_dec(v_a_473_);
lean_dec_ref(v_tail_467_);
return v___x_472_;
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
lean_dec_ref_known(v___x_472_, 1);
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_474_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_455_, v_tail_467_, v___x_477_, v___x_478_, v_a_473_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec_ref(v_tail_467_);
return v___x_479_;
}
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
lean_dec_ref_known(v___x_472_, 1);
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_474_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_455_, v_tail_467_, v___x_480_, v___x_481_, v_a_473_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec_ref(v_tail_467_);
return v___x_482_;
}
}
}
else
{
lean_dec_ref(v_tail_467_);
return v___x_472_;
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
lean_dec_ref(v_root_466_);
v___x_483_ = lean_nat_sub(v_start_458_, v_tailOff_469_);
lean_dec(v_tailOff_469_);
v___x_484_ = lean_array_get_size(v_tail_467_);
v___x_485_ = lean_nat_dec_lt(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec(v___x_483_);
lean_dec_ref(v_tail_467_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_init_457_);
return v___x_486_;
}
else
{
uint8_t v___x_487_; 
v___x_487_ = lean_nat_dec_le(v___x_484_, v___x_484_);
if (v___x_487_ == 0)
{
if (v___x_485_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v___x_483_);
lean_dec_ref(v_tail_467_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_init_457_);
return v___x_488_;
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_usize_of_nat(v___x_483_);
lean_dec(v___x_483_);
v___x_490_ = lean_usize_of_nat(v___x_484_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_455_, v_tail_467_, v___x_489_, v___x_490_, v_init_457_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec_ref(v_tail_467_);
return v___x_491_;
}
}
else
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_usize_of_nat(v___x_483_);
lean_dec(v___x_483_);
v___x_493_ = lean_usize_of_nat(v___x_484_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_455_, v_tail_467_, v___x_492_, v___x_493_, v_init_457_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec_ref(v_tail_467_);
return v___x_494_;
}
}
}
}
else
{
lean_object* v_root_495_; lean_object* v_tail_496_; lean_object* v___x_497_; 
v_root_495_ = lean_ctor_get(v_t_456_, 0);
lean_inc_ref(v_root_495_);
v_tail_496_ = lean_ctor_get(v_t_456_, 1);
lean_inc_ref(v_tail_496_);
lean_dec_ref(v_t_456_);
v___x_497_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_455_, v_root_495_, v_init_457_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
v___x_499_ = lean_array_get_size(v_tail_496_);
v___x_500_ = lean_nat_dec_lt(v___x_464_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec(v_a_498_);
lean_dec_ref(v_tail_496_);
return v___x_497_;
}
else
{
uint8_t v___x_501_; 
v___x_501_ = lean_nat_dec_le(v___x_499_, v___x_499_);
if (v___x_501_ == 0)
{
if (v___x_500_ == 0)
{
lean_dec(v_a_498_);
lean_dec_ref(v_tail_496_);
return v___x_497_;
}
else
{
size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
lean_dec_ref_known(v___x_497_, 1);
v___x_502_ = ((size_t)0ULL);
v___x_503_ = lean_usize_of_nat(v___x_499_);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_455_, v_tail_496_, v___x_502_, v___x_503_, v_a_498_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec_ref(v_tail_496_);
return v___x_504_;
}
}
else
{
size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
lean_dec_ref_known(v___x_497_, 1);
v___x_505_ = ((size_t)0ULL);
v___x_506_ = lean_usize_of_nat(v___x_499_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_455_, v_tail_496_, v___x_505_, v___x_506_, v_a_498_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec_ref(v_tail_496_);
return v___x_507_;
}
}
}
else
{
lean_dec_ref(v_tail_496_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3___boxed(lean_object* v_auxDeclToFullName_508_, lean_object* v_t_509_, lean_object* v_init_510_, lean_object* v_start_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_508_, v_t_509_, v_init_510_, v_start_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v_start_511_);
lean_dec(v_auxDeclToFullName_508_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(lean_object* v_auxDeclToFullName_518_, lean_object* v_lctx_519_, lean_object* v_init_520_, lean_object* v_start_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_decls_527_; lean_object* v___x_528_; 
v_decls_527_ = lean_ctor_get(v_lctx_519_, 1);
lean_inc_ref(v_decls_527_);
lean_dec_ref(v_lctx_519_);
v___x_528_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_518_, v_decls_527_, v_init_520_, v_start_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2___boxed(lean_object* v_auxDeclToFullName_529_, lean_object* v_lctx_530_, lean_object* v_init_531_, lean_object* v_start_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_529_, v_lctx_530_, v_init_531_, v_start_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v_start_532_);
lean_dec(v_auxDeclToFullName_529_);
return v_res_538_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_539_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(32u);
v___x_543_ = lean_mk_empty_array_with_capacity(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3(void){
_start:
{
size_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_unsigned_to_nat(32u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2);
v___x_550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_546_);
lean_ctor_set(v___x_550_, 3, v___x_546_);
lean_ctor_set_usize(v___x_550_, 4, v___x_545_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = lean_box(1);
v___x_552_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3);
v___x_553_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1);
v___x_554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
lean_ctor_set(v___x_554_, 2, v___x_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(lean_object* v_lctx_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_auxDeclToFullName_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_auxDeclToFullName_561_ = lean_ctor_get(v_lctx_555_, 2);
lean_inc(v_auxDeclToFullName_561_);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4);
v___x_564_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_561_, v_lctx_555_, v___x_563_, v___x_562_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v_auxDeclToFullName_561_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___boxed(lean_object* v_lctx_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_ks_576_; lean_object* v_vs_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_601_; 
v_ks_576_ = lean_ctor_get(v_x_572_, 0);
v_vs_577_ = lean_ctor_get(v_x_572_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_601_ == 0)
{
v___x_579_ = v_x_572_;
v_isShared_580_ = v_isSharedCheck_601_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_vs_577_);
lean_inc(v_ks_576_);
lean_dec(v_x_572_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_601_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_array_get_size(v_ks_576_);
v___x_582_ = lean_nat_dec_lt(v_x_573_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
lean_dec(v_x_573_);
v___x_583_ = lean_array_push(v_ks_576_, v_x_574_);
v___x_584_ = lean_array_push(v_vs_577_, v_x_575_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v___x_584_);
lean_ctor_set(v___x_579_, 0, v___x_583_);
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
lean_object* v_k_x27_588_; uint8_t v___x_589_; 
v_k_x27_588_ = lean_array_fget_borrowed(v_ks_576_, v_x_573_);
v___x_589_ = l_Lean_instBEqMVarId_beq(v_x_574_, v_k_x27_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_591_; 
if (v_isShared_580_ == 0)
{
v___x_591_ = v___x_579_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_ks_576_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_vs_577_);
v___x_591_ = v_reuseFailAlloc_595_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_x_573_, v___x_592_);
lean_dec(v_x_573_);
v_x_572_ = v___x_591_;
v_x_573_ = v___x_593_;
goto _start;
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_596_ = lean_array_fset(v_ks_576_, v_x_573_, v_x_574_);
v___x_597_ = lean_array_fset(v_vs_577_, v_x_573_, v_x_575_);
lean_dec(v_x_573_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v___x_597_);
lean_ctor_set(v___x_579_, 0, v___x_596_);
v___x_599_ = v___x_579_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(lean_object* v_n_602_, lean_object* v_k_603_, lean_object* v_v_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_n_602_, v___x_605_, v_k_603_, v_v_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(lean_object* v_x_608_, size_t v_x_609_, size_t v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v_es_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v_j_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_es_613_ = lean_ctor_get(v_x_608_, 0);
v___x_614_ = ((size_t)31ULL);
v___x_615_ = lean_usize_land(v_x_609_, v___x_614_);
v_j_616_ = lean_usize_to_nat(v___x_615_);
v___x_617_ = lean_array_get_size(v_es_613_);
v___x_618_ = lean_nat_dec_lt(v_j_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v_j_616_);
lean_dec(v_x_612_);
lean_dec(v_x_611_);
return v_x_608_;
}
else
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_657_; 
lean_inc_ref(v_es_613_);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_608_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_x_608_, 0);
lean_dec(v_unused_658_);
v___x_620_ = v_x_608_;
v_isShared_621_ = v_isSharedCheck_657_;
goto v_resetjp_619_;
}
else
{
lean_dec(v_x_608_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_657_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_v_622_; lean_object* v___x_623_; lean_object* v_xs_x27_624_; lean_object* v___y_626_; 
v_v_622_ = lean_array_fget(v_es_613_, v_j_616_);
v___x_623_ = lean_box(0);
v_xs_x27_624_ = lean_array_fset(v_es_613_, v_j_616_, v___x_623_);
switch(lean_obj_tag(v_v_622_))
{
case 0:
{
lean_object* v_key_631_; lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_642_; 
v_key_631_ = lean_ctor_get(v_v_622_, 0);
v_val_632_ = lean_ctor_get(v_v_622_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_v_622_);
if (v_isSharedCheck_642_ == 0)
{
v___x_634_ = v_v_622_;
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_inc(v_key_631_);
lean_dec(v_v_622_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_642_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = l_Lean_instBEqMVarId_beq(v_x_611_, v_key_631_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_del_object(v___x_634_);
v___x_637_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_631_, v_val_632_, v_x_611_, v_x_612_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
v___y_626_ = v___x_638_;
goto v___jp_625_;
}
else
{
lean_object* v___x_640_; 
lean_dec(v_val_632_);
lean_dec(v_key_631_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_x_612_);
lean_ctor_set(v___x_634_, 0, v_x_611_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_x_611_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_x_612_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
v___y_626_ = v___x_640_;
goto v___jp_625_;
}
}
}
}
case 1:
{
lean_object* v_node_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_655_; 
v_node_643_ = lean_ctor_get(v_v_622_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_v_622_);
if (v_isSharedCheck_655_ == 0)
{
v___x_645_ = v_v_622_;
v_isShared_646_ = v_isSharedCheck_655_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_node_643_);
lean_dec(v_v_622_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_655_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_647_ = ((size_t)5ULL);
v___x_648_ = lean_usize_shift_right(v_x_609_, v___x_647_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_x_610_, v___x_649_);
v___x_651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_node_643_, v___x_648_, v___x_650_, v_x_611_, v_x_612_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_651_);
v___x_653_ = v___x_645_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
v___y_626_ = v___x_653_;
goto v___jp_625_;
}
}
}
default: 
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_x_611_);
lean_ctor_set(v___x_656_, 1, v_x_612_);
v___y_626_ = v___x_656_;
goto v___jp_625_;
}
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_array_fset(v_xs_x27_624_, v_j_616_, v___y_626_);
lean_dec(v_j_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_627_);
v___x_629_ = v___x_620_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
else
{
lean_object* v_ks_659_; lean_object* v_vs_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_680_; 
v_ks_659_ = lean_ctor_get(v_x_608_, 0);
v_vs_660_ = lean_ctor_get(v_x_608_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_608_);
if (v_isSharedCheck_680_ == 0)
{
v___x_662_ = v_x_608_;
v_isShared_663_ = v_isSharedCheck_680_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_vs_660_);
lean_inc(v_ks_659_);
lean_dec(v_x_608_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_680_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_ks_659_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_vs_660_);
v___x_665_ = v_reuseFailAlloc_679_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v_newNode_666_; uint8_t v___y_668_; size_t v___x_674_; uint8_t v___x_675_; 
v_newNode_666_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v___x_665_, v_x_611_, v_x_612_);
v___x_674_ = ((size_t)7ULL);
v___x_675_ = lean_usize_dec_le(v___x_674_, v_x_610_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_676_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_666_);
v___x_677_ = lean_unsigned_to_nat(4u);
v___x_678_ = lean_nat_dec_lt(v___x_676_, v___x_677_);
lean_dec(v___x_676_);
v___y_668_ = v___x_678_;
goto v___jp_667_;
}
else
{
v___y_668_ = v___x_675_;
goto v___jp_667_;
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
lean_object* v_ks_669_; lean_object* v_vs_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_ks_669_ = lean_ctor_get(v_newNode_666_, 0);
lean_inc_ref(v_ks_669_);
v_vs_670_ = lean_ctor_get(v_newNode_666_, 1);
lean_inc_ref(v_vs_670_);
lean_dec_ref(v_newNode_666_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0);
v___x_673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_x_610_, v_ks_669_, v_vs_670_, v___x_671_, v___x_672_);
lean_dec_ref(v_vs_670_);
lean_dec_ref(v_ks_669_);
return v___x_673_;
}
else
{
return v_newNode_666_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(size_t v_depth_681_, lean_object* v_keys_682_, lean_object* v_vals_683_, lean_object* v_i_684_, lean_object* v_entries_685_){
_start:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_array_get_size(v_keys_682_);
v___x_687_ = lean_nat_dec_lt(v_i_684_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v_i_684_);
return v_entries_685_;
}
else
{
lean_object* v_k_688_; lean_object* v_v_689_; uint64_t v___x_690_; size_t v_h_691_; size_t v___x_692_; lean_object* v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v_h_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_k_688_ = lean_array_fget_borrowed(v_keys_682_, v_i_684_);
v_v_689_ = lean_array_fget_borrowed(v_vals_683_, v_i_684_);
v___x_690_ = l_Lean_instHashableMVarId_hash(v_k_688_);
v_h_691_ = lean_uint64_to_usize(v___x_690_);
v___x_692_ = ((size_t)5ULL);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = ((size_t)1ULL);
v___x_695_ = lean_usize_sub(v_depth_681_, v___x_694_);
v___x_696_ = lean_usize_mul(v___x_692_, v___x_695_);
v_h_697_ = lean_usize_shift_right(v_h_691_, v___x_696_);
v___x_698_ = lean_nat_add(v_i_684_, v___x_693_);
lean_dec(v_i_684_);
lean_inc(v_v_689_);
lean_inc(v_k_688_);
v___x_699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_entries_685_, v_h_697_, v_depth_681_, v_k_688_, v_v_689_);
v_i_684_ = v___x_698_;
v_entries_685_ = v___x_699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg___boxed(lean_object* v_depth_701_, lean_object* v_keys_702_, lean_object* v_vals_703_, lean_object* v_i_704_, lean_object* v_entries_705_){
_start:
{
size_t v_depth_boxed_706_; lean_object* v_res_707_; 
v_depth_boxed_706_ = lean_unbox_usize(v_depth_701_);
lean_dec(v_depth_701_);
v_res_707_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_boxed_706_, v_keys_702_, v_vals_703_, v_i_704_, v_entries_705_);
lean_dec_ref(v_vals_703_);
lean_dec_ref(v_keys_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
size_t v_x_4886__boxed_713_; size_t v_x_4887__boxed_714_; lean_object* v_res_715_; 
v_x_4886__boxed_713_ = lean_unbox_usize(v_x_709_);
lean_dec(v_x_709_);
v_x_4887__boxed_714_ = lean_unbox_usize(v_x_710_);
lean_dec(v_x_710_);
v_res_715_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_708_, v_x_4886__boxed_713_, v_x_4887__boxed_714_, v_x_711_, v_x_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
uint64_t v___x_719_; size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; 
v___x_719_ = l_Lean_instHashableMVarId_hash(v_x_717_);
v___x_720_ = lean_uint64_to_usize(v___x_719_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_716_, v___x_720_, v___x_721_, v_x_717_, v_x_718_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(lean_object* v_mvarId_723_, lean_object* v_val_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; lean_object* v_mctx_728_; lean_object* v_cache_729_; lean_object* v_zetaDeltaFVarIds_730_; lean_object* v_postponed_731_; lean_object* v_diag_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_761_; 
v___x_727_ = lean_st_ref_take(v___y_725_);
v_mctx_728_ = lean_ctor_get(v___x_727_, 0);
v_cache_729_ = lean_ctor_get(v___x_727_, 1);
v_zetaDeltaFVarIds_730_ = lean_ctor_get(v___x_727_, 2);
v_postponed_731_ = lean_ctor_get(v___x_727_, 3);
v_diag_732_ = lean_ctor_get(v___x_727_, 4);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_761_ == 0)
{
v___x_734_ = v___x_727_;
v_isShared_735_ = v_isSharedCheck_761_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_diag_732_);
lean_inc(v_postponed_731_);
lean_inc(v_zetaDeltaFVarIds_730_);
lean_inc(v_cache_729_);
lean_inc(v_mctx_728_);
lean_dec(v___x_727_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_761_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_depth_736_; lean_object* v_levelAssignDepth_737_; lean_object* v_lmvarCounter_738_; lean_object* v_mvarCounter_739_; lean_object* v_lDecls_740_; lean_object* v_decls_741_; lean_object* v_userNames_742_; lean_object* v_lAssignment_743_; lean_object* v_eAssignment_744_; lean_object* v_dAssignment_745_; lean_object* v_instanceTypedMVars_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_760_; 
v_depth_736_ = lean_ctor_get(v_mctx_728_, 0);
v_levelAssignDepth_737_ = lean_ctor_get(v_mctx_728_, 1);
v_lmvarCounter_738_ = lean_ctor_get(v_mctx_728_, 2);
v_mvarCounter_739_ = lean_ctor_get(v_mctx_728_, 3);
v_lDecls_740_ = lean_ctor_get(v_mctx_728_, 4);
v_decls_741_ = lean_ctor_get(v_mctx_728_, 5);
v_userNames_742_ = lean_ctor_get(v_mctx_728_, 6);
v_lAssignment_743_ = lean_ctor_get(v_mctx_728_, 7);
v_eAssignment_744_ = lean_ctor_get(v_mctx_728_, 8);
v_dAssignment_745_ = lean_ctor_get(v_mctx_728_, 9);
v_instanceTypedMVars_746_ = lean_ctor_get(v_mctx_728_, 10);
v_isSharedCheck_760_ = !lean_is_exclusive(v_mctx_728_);
if (v_isSharedCheck_760_ == 0)
{
v___x_748_ = v_mctx_728_;
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_instanceTypedMVars_746_);
lean_inc(v_dAssignment_745_);
lean_inc(v_eAssignment_744_);
lean_inc(v_lAssignment_743_);
lean_inc(v_userNames_742_);
lean_inc(v_decls_741_);
lean_inc(v_lDecls_740_);
lean_inc(v_mvarCounter_739_);
lean_inc(v_lmvarCounter_738_);
lean_inc(v_levelAssignDepth_737_);
lean_inc(v_depth_736_);
lean_dec(v_mctx_728_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_744_, v_mvarId_723_, v_val_724_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 8, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_depth_736_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_levelAssignDepth_737_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_lmvarCounter_738_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_mvarCounter_739_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_lDecls_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 5, v_decls_741_);
lean_ctor_set(v_reuseFailAlloc_759_, 6, v_userNames_742_);
lean_ctor_set(v_reuseFailAlloc_759_, 7, v_lAssignment_743_);
lean_ctor_set(v_reuseFailAlloc_759_, 8, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_759_, 9, v_dAssignment_745_);
lean_ctor_set(v_reuseFailAlloc_759_, 10, v_instanceTypedMVars_746_);
v___x_752_ = v_reuseFailAlloc_759_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_752_);
v___x_754_ = v___x_734_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_cache_729_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_zetaDeltaFVarIds_730_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_postponed_731_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_diag_732_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_st_ref_put(v___y_725_, v___x_754_);
v___x_756_ = lean_box(0);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(lean_object* v_mvarId_762_, lean_object* v_val_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_762_, v_val_763_, v___y_764_);
lean_dec(v___y_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars(lean_object* v_mvarId_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_767_);
v___x_774_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_767_, v___x_773_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_775_; 
lean_dec_ref_known(v___x_774_, 1);
lean_inc(v_mvarId_767_);
v___x_775_ = l_Lean_MVarId_getDecl(v_mvarId_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v_userName_777_; lean_object* v_lctx_778_; lean_object* v_type_779_; lean_object* v_localInstances_780_; lean_object* v___x_781_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v_userName_777_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_userName_777_);
v_lctx_778_ = lean_ctor_get(v_a_776_, 1);
lean_inc_ref(v_lctx_778_);
v_type_779_ = lean_ctor_get(v_a_776_, 2);
lean_inc_ref(v_type_779_);
v_localInstances_780_ = lean_ctor_get(v_a_776_, 4);
lean_inc_ref(v_localInstances_780_);
lean_dec(v_a_776_);
v___x_781_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_778_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v_a_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_779_, v_a_769_);
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = 2;
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_782_, v_localInstances_780_, v_a_784_, v___x_785_, v_userName_777_, v___x_786_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_n(v_a_788_, 2);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_767_, v_a_788_, v_a_769_);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_798_);
v___x_791_ = v___x_789_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_dec(v___x_789_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = l_Lean_Expr_mvarId_x21(v_a_788_);
lean_dec(v_a_788_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_mvarId_767_);
v_a_799_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_787_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_787_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_localInstances_780_);
lean_dec_ref(v_type_779_);
lean_dec(v_userName_777_);
lean_dec(v_mvarId_767_);
v_a_807_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_781_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_781_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_mvarId_767_);
v_a_815_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_775_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_775_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_mvarId_767_);
v_a_823_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_774_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_774_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars___boxed(lean_object* v_mvarId_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_MVarId_instantiateGoalMVars(v_mvarId_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(lean_object* v_mvarId_838_, lean_object* v_val_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_838_, v_val_839_, v___y_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(lean_object* v_mvarId_846_, lean_object* v_val_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(v_mvarId_846_, v_val_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(lean_object* v_00_u03b4_854_, lean_object* v_t_855_, lean_object* v_k_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_855_, v_k_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b4_858_, lean_object* v_t_859_, lean_object* v_k_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(v_00_u03b4_858_, v_t_859_, v_k_860_);
lean_dec(v_k_860_);
lean_dec(v_t_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_x_863_, v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, size_t v_x_869_, size_t v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_868_, v_x_869_, v_x_870_, v_x_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
size_t v_x_5246__boxed_880_; size_t v_x_5247__boxed_881_; lean_object* v_res_882_; 
v_x_5246__boxed_880_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_x_5247__boxed_881_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_res_882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_874_, v_x_875_, v_x_5246__boxed_880_, v_x_5247__boxed_881_, v_x_878_, v_x_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_883_, lean_object* v_n_884_, lean_object* v_k_885_, lean_object* v_v_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v_n_884_, v_k_885_, v_v_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_888_, size_t v_depth_889_, lean_object* v_keys_890_, lean_object* v_vals_891_, lean_object* v_heq_892_, lean_object* v_i_893_, lean_object* v_entries_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_889_, v_keys_890_, v_vals_891_, v_i_893_, v_entries_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(lean_object* v_00_u03b2_896_, lean_object* v_depth_897_, lean_object* v_keys_898_, lean_object* v_vals_899_, lean_object* v_heq_900_, lean_object* v_i_901_, lean_object* v_entries_902_){
_start:
{
size_t v_depth_boxed_903_; lean_object* v_res_904_; 
v_depth_boxed_903_ = lean_unbox_usize(v_depth_897_);
lean_dec(v_depth_897_);
v_res_904_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(v_00_u03b2_896_, v_depth_boxed_903_, v_keys_898_, v_vals_899_, v_heq_900_, v_i_901_, v_entries_902_);
lean_dec_ref(v_vals_899_);
lean_dec_ref(v_keys_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_x_906_, v_x_907_, v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(lean_object* v_k_911_, lean_object* v_b_912_, lean_object* v_c_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_919_ = lean_apply_7(v_k_911_, v_b_912_, v_c_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(lean_object* v_k_920_, lean_object* v_b_921_, lean_object* v_c_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(v_k_920_, v_b_921_, v_c_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(lean_object* v_e_929_, lean_object* v_k_930_, uint8_t v_cleanupAnnotations_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___f_937_; uint8_t v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_937_, 0, v_k_930_);
v___x_938_ = 1;
v___x_939_ = 0;
v___x_940_ = lean_box(0);
v___x_941_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_929_, v___x_938_, v___x_939_, v___x_938_, v___x_939_, v___x_940_, v___f_937_, v_cleanupAnnotations_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v_a_950_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_941_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_941_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_958_, lean_object* v_k_959_, lean_object* v_cleanupAnnotations_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_966_; lean_object* v_res_967_; 
v_cleanupAnnotations_boxed_966_ = lean_unbox(v_cleanupAnnotations_960_);
v_res_967_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_958_, v_k_959_, v_cleanupAnnotations_boxed_966_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(lean_object* v_00_u03b1_968_, lean_object* v_e_969_, lean_object* v_k_970_, uint8_t v_cleanupAnnotations_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_969_, v_k_970_, v_cleanupAnnotations_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___boxed(lean_object* v_00_u03b1_978_, lean_object* v_e_979_, lean_object* v_k_980_, lean_object* v_cleanupAnnotations_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_987_; lean_object* v_res_988_; 
v_cleanupAnnotations_boxed_987_ = lean_unbox(v_cleanupAnnotations_981_);
v_res_988_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(v_00_u03b1_978_, v_e_979_, v_k_980_, v_cleanupAnnotations_boxed_987_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(lean_object* v_mvarId_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_989_, v_x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_996_) == 0)
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
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_a_1005_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_996_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_996_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg___boxed(lean_object* v_mvarId_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1013_, v_x_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(lean_object* v_00_u03b1_1021_, lean_object* v_mvarId_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1022_, v_x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_mvarId_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(v_00_u03b1_1030_, v_mvarId_1031_, v_x_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t v___x_1039_, uint8_t v___x_1040_, lean_object* v_xs_1041_, lean_object* v_body_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = 1;
v___x_1049_ = l_Lean_Meta_mkForallFVars(v_xs_1041_, v_body_1042_, v___x_1039_, v___x_1040_, v___x_1040_, v___x_1048_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object* v___x_1050_, lean_object* v___x_1051_, lean_object* v_xs_1052_, lean_object* v_body_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v___x_1951__boxed_1059_; uint8_t v___x_1952__boxed_1060_; lean_object* v_res_1061_; 
v___x_1951__boxed_1059_ = lean_unbox(v___x_1050_);
v___x_1952__boxed_1060_ = lean_unbox(v___x_1051_);
v_res_1061_ = l_Lean_MVarId_abstractMVars___lam__0(v___x_1951__boxed_1059_, v___x_1952__boxed_1060_, v_xs_1052_, v_body_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec_ref(v_xs_1052_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object* v_a_1062_, uint8_t v___x_1063_, lean_object* v___f_1064_, lean_object* v_mvarId_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_abstractMVars(v_a_1062_, v___x_1063_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_mvars_1073_; lean_object* v_expr_1074_; lean_object* v___x_1075_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_mvars_1073_ = lean_ctor_get(v_a_1072_, 1);
lean_inc_ref(v_mvars_1073_);
v_expr_1074_ = lean_ctor_get(v_a_1072_, 2);
lean_inc_ref(v_expr_1074_);
lean_dec(v_a_1072_);
v___x_1075_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_expr_1074_, v___f_1064_, v___x_1063_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
lean_inc(v_mvarId_1065_);
v___x_1077_ = l_Lean_MVarId_getTag(v_mvarId_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1076_, v_a_1078_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_n(v_a_1080_, 2);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = l_Lean_mkAppN(v_a_1080_, v_mvars_1073_);
lean_dec_ref(v_mvars_1073_);
v___x_1082_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1065_, v___x_1081_, v___y_1067_);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___x_1082_, 0);
lean_dec(v_unused_1091_);
v___x_1084_ = v___x_1082_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v___x_1082_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = l_Lean_Expr_mvarId_x21(v_a_1080_);
lean_dec(v_a_1080_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_mvars_1073_);
lean_dec(v_mvarId_1065_);
v_a_1092_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1079_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1079_);
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
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_a_1076_);
lean_dec_ref(v_mvars_1073_);
lean_dec(v_mvarId_1065_);
v_a_1100_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1077_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1077_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_mvars_1073_);
lean_dec(v_mvarId_1065_);
v_a_1108_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1075_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1075_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_mvarId_1065_);
lean_dec_ref(v___f_1064_);
v_a_1116_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1071_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1071_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object* v_a_1124_, lean_object* v___x_1125_, lean_object* v___f_1126_, lean_object* v_mvarId_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v___x_1977__boxed_1133_; lean_object* v_res_1134_; 
v___x_1977__boxed_1133_ = lean_unbox(v___x_1125_);
v_res_1134_ = l_Lean_MVarId_abstractMVars___lam__1(v_a_1124_, v___x_1977__boxed_1133_, v___f_1126_, v_mvarId_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars(lean_object* v_mvarId_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1135_);
v___x_1142_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1135_, v___x_1141_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref_known(v___x_1142_, 1);
lean_inc(v_mvarId_1135_);
v___x_1143_ = l_Lean_MVarId_getType(v_mvarId_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1161_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_1144_, v_a_1137_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1161_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1161_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Lean_Expr_hasExprMVar(v_a_1146_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1152_; 
lean_dec(v_a_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_mvarId_1135_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_mvarId_1135_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; 
lean_del_object(v___x_1148_);
v___x_1154_ = 0;
v___x_1155_ = lean_box(v___x_1154_);
v___x_1156_ = lean_box(v___x_1150_);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1157_, 0, v___x_1155_);
lean_closure_set(v___f_1157_, 1, v___x_1156_);
v___x_1158_ = lean_box(v___x_1154_);
lean_inc(v_mvarId_1135_);
v___f_1159_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1159_, 0, v_a_1146_);
lean_closure_set(v___f_1159_, 1, v___x_1158_);
lean_closure_set(v___f_1159_, 2, v___f_1157_);
lean_closure_set(v___f_1159_, 3, v_mvarId_1135_);
v___x_1160_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1135_, v___f_1159_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_mvarId_1135_);
v_a_1162_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1143_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1143_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_mvarId_1135_);
v_a_1170_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1142_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1142_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___boxed(lean_object* v_mvarId_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_MVarId_abstractMVars(v_mvarId_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object* v_mvarId_1185_, lean_object* v___x_1186_, lean_object* v_f_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
lean_inc(v_mvarId_1185_);
v___x_1193_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1185_, v___x_1186_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1194_; 
lean_dec_ref_known(v___x_1193_, 1);
lean_inc(v_mvarId_1185_);
v___x_1194_ = l_Lean_MVarId_getTag(v_mvarId_1185_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
lean_inc(v_mvarId_1185_);
v___x_1196_ = l_Lean_MVarId_getType(v_mvarId_1185_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
lean_inc(v___y_1191_);
lean_inc_ref(v___y_1190_);
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
v___x_1198_ = lean_apply_6(v_f_1187_, v_a_1197_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1199_, v_a_1195_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v___y_1188_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1210_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_n(v_a_1201_, 2);
lean_dec_ref_known(v___x_1200_, 1);
v___x_1202_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1185_, v_a_1201_, v___y_1189_);
lean_dec(v___y_1189_);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v___x_1202_, 0);
lean_dec(v_unused_1211_);
v___x_1204_ = v___x_1202_;
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v___x_1202_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = l_Lean_Expr_mvarId_x21(v_a_1201_);
lean_dec(v_a_1201_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v___y_1189_);
lean_dec(v_mvarId_1185_);
v_a_1212_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1200_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1200_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_a_1195_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v_mvarId_1185_);
v_a_1220_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1198_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1198_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_a_1195_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_f_1187_);
lean_dec(v_mvarId_1185_);
v_a_1228_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1196_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1196_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_f_1187_);
lean_dec(v_mvarId_1185_);
v_a_1236_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1194_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1194_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_f_1187_);
lean_dec(v_mvarId_1185_);
v_a_1244_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1193_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1193_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0___boxed(lean_object* v_mvarId_1252_, lean_object* v___x_1253_, lean_object* v_f_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_MVarId_transformTarget___lam__0(v_mvarId_1252_, v___x_1253_, v_f_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object* v_mvarId_1261_, lean_object* v_f_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; 
v___x_1268_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1261_);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_MVarId_transformTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1269_, 0, v_mvarId_1261_);
lean_closure_set(v___f_1269_, 1, v___x_1268_);
lean_closure_set(v___f_1269_, 2, v_f_1262_);
v___x_1270_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1261_, v___f_1269_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___boxed(lean_object* v_mvarId_1271_, lean_object* v_f_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_MVarId_transformTarget(v_mvarId_1271_, v_f_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object* v_mvarId_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_MVarId_unfoldReducible___closed__0));
v___x_1287_ = l_Lean_MVarId_transformTarget(v_mvarId_1280_, v___x_1286_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible___boxed(lean_object* v_mvarId_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_MVarId_unfoldReducible(v_mvarId_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object* v_x_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Core_betaReduce(v_x_1295_, v___y_1298_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_MVarId_betaReduce___lam__0(v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object* v_mvarId_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___f_1316_; lean_object* v___x_1317_; 
v___f_1316_ = ((lean_object*)(l_Lean_MVarId_betaReduce___closed__0));
v___x_1317_ = l_Lean_MVarId_transformTarget(v_mvarId_1310_, v___f_1316_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___boxed(lean_object* v_mvarId_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_MVarId_betaReduce(v_mvarId_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
return v_res_1324_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_box(0);
v___x_1329_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__1));
v___x_1330_ = l_Lean_mkConst(v___x_1329_, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__5));
v___x_1338_ = l_Lean_mkConst(v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object* v_mvarId_1339_, lean_object* v___x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
lean_inc(v_mvarId_1339_);
v___x_1346_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1339_, v___x_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref_known(v___x_1346_, 1);
lean_inc(v_mvarId_1339_);
v___x_1347_ = l_Lean_MVarId_getType(v_mvarId_1339_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1402_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1402_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1402_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
uint8_t v___x_1352_; 
lean_inc(v_a_1348_);
v___x_1352_ = l_Lean_Expr_isFalse(v_a_1348_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_del_object(v___x_1350_);
lean_inc(v_a_1348_);
v___x_1353_ = l_Lean_mkNot(v_a_1348_);
v___x_1354_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__2, &l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2);
v___x_1355_ = l_Lean_mkArrow(v___x_1353_, v___x_1354_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
lean_inc(v_mvarId_1339_);
v___x_1357_ = l_Lean_MVarId_getTag(v_mvarId_1339_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1356_, v_a_1358_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1372_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_n(v_a_1360_, 2);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__6, &l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6);
v___x_1362_ = l_Lean_mkAppB(v___x_1361_, v_a_1348_, v_a_1360_);
v___x_1363_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1339_, v___x_1362_, v___y_1342_);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1363_, 0);
lean_dec(v_unused_1373_);
v___x_1365_ = v___x_1363_;
v_isShared_1366_ = v_isSharedCheck_1372_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v___x_1363_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1372_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = l_Lean_Expr_mvarId_x21(v_a_1360_);
lean_dec(v_a_1360_);
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1368_);
v___x_1370_ = v___x_1365_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1348_);
lean_dec(v_mvarId_1339_);
v_a_1374_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1359_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1359_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1356_);
lean_dec(v_a_1348_);
lean_dec(v_mvarId_1339_);
v_a_1382_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1357_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1357_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_a_1348_);
lean_dec(v_mvarId_1339_);
v_a_1390_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1355_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1355_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_dec(v_a_1348_);
lean_dec(v_mvarId_1339_);
v___x_1398_ = lean_box(0);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1398_);
v___x_1400_ = v___x_1350_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_mvarId_1339_);
v_a_1403_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1347_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1347_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_mvarId_1339_);
v_a_1411_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1346_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1346_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object* v_mvarId_1419_, lean_object* v___x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_MVarId_byContra_x3f___lam__0(v_mvarId_1419_, v___x_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object* v_mvarId_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; 
v___x_1437_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___closed__1));
lean_inc(v_mvarId_1431_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_MVarId_byContra_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1438_, 0, v_mvarId_1431_);
lean_closure_set(v___f_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1431_, v___f_1438_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___boxed(lean_object* v_mvarId_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_1447_, size_t v_sz_1448_, size_t v_i_1449_, lean_object* v_b_1450_){
_start:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_usize_dec_lt(v_i_1449_, v_sz_1448_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_b_1450_);
return v___x_1453_;
}
else
{
lean_object* v_snd_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1472_; 
v_snd_1454_ = lean_ctor_get(v_b_1450_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_b_1450_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_b_1450_, 0);
lean_dec(v_unused_1473_);
v___x_1456_ = v_b_1450_;
v_isShared_1457_ = v_isSharedCheck_1472_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_snd_1454_);
lean_dec(v_b_1450_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1472_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v_a_1460_; lean_object* v_a_1467_; 
v___x_1458_ = lean_box(0);
v_a_1467_ = lean_array_uget_borrowed(v_as_1447_, v_i_1449_);
if (lean_obj_tag(v_a_1467_) == 0)
{
v_a_1460_ = v_snd_1454_;
goto v___jp_1459_;
}
else
{
lean_object* v_val_1468_; uint8_t v___x_1469_; 
v_val_1468_ = lean_ctor_get(v_a_1467_, 0);
v___x_1469_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1468_);
if (v___x_1469_ == 0)
{
v_a_1460_ = v_snd_1454_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = l_Lean_LocalDecl_fvarId(v_val_1468_);
v___x_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v_snd_1454_);
v_a_1460_ = v___x_1471_;
goto v___jp_1459_;
}
}
v___jp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 1, v_a_1460_);
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1462_ = v___x_1456_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1460_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
size_t v___x_1463_; size_t v___x_1464_; 
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_add(v_i_1449_, v___x_1463_);
v_i_1449_ = v___x_1464_;
v_b_1450_ = v___x_1462_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_1474_, lean_object* v_sz_1475_, lean_object* v_i_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_){
_start:
{
size_t v_sz_boxed_1479_; size_t v_i_boxed_1480_; lean_object* v_res_1481_; 
v_sz_boxed_1479_ = lean_unbox_usize(v_sz_1475_);
lean_dec(v_sz_1475_);
v_i_boxed_1480_ = lean_unbox_usize(v_i_1476_);
lean_dec(v_i_1476_);
v_res_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1474_, v_sz_boxed_1479_, v_i_boxed_1480_, v_b_1477_);
lean_dec_ref(v_as_1474_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(lean_object* v_as_1482_, size_t v_sz_1483_, size_t v_i_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_usize_dec_lt(v_i_1484_, v_sz_1483_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_b_1485_);
return v___x_1492_;
}
else
{
lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1511_; 
v_snd_1493_ = lean_ctor_get(v_b_1485_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_b_1485_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_b_1485_, 0);
lean_dec(v_unused_1512_);
v___x_1495_ = v_b_1485_;
v_isShared_1496_ = v_isSharedCheck_1511_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_dec(v_b_1485_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1511_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v_a_1499_; lean_object* v_a_1506_; 
v___x_1497_ = lean_box(0);
v_a_1506_ = lean_array_uget_borrowed(v_as_1482_, v_i_1484_);
if (lean_obj_tag(v_a_1506_) == 0)
{
v_a_1499_ = v_snd_1493_;
goto v___jp_1498_;
}
else
{
lean_object* v_val_1507_; uint8_t v___x_1508_; 
v_val_1507_ = lean_ctor_get(v_a_1506_, 0);
v___x_1508_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1507_);
if (v___x_1508_ == 0)
{
v_a_1499_ = v_snd_1493_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = l_Lean_LocalDecl_fvarId(v_val_1507_);
v___x_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_snd_1493_);
v_a_1499_ = v___x_1510_;
goto v___jp_1498_;
}
}
v___jp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v_a_1499_);
lean_ctor_set(v___x_1495_, 0, v___x_1497_);
v___x_1501_ = v___x_1495_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_a_1499_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((size_t)1ULL);
v___x_1503_ = lean_usize_add(v_i_1484_, v___x_1502_);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1482_, v_sz_1483_, v___x_1503_, v___x_1501_);
return v___x_1504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
size_t v_sz_boxed_1522_; size_t v_i_boxed_1523_; lean_object* v_res_1524_; 
v_sz_boxed_1522_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1523_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_1513_, v_sz_boxed_1522_, v_i_boxed_1523_, v_b_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_as_1513_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object* v_init_1525_, lean_object* v_n_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
if (lean_obj_tag(v_n_1526_) == 0)
{
lean_object* v_cs_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; size_t v_sz_1536_; size_t v___x_1537_; lean_object* v___x_1538_; 
v_cs_1533_ = lean_ctor_get(v_n_1526_, 0);
v___x_1534_ = lean_box(0);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_b_1527_);
v_sz_1536_ = lean_array_size(v_cs_1533_);
v___x_1537_ = ((size_t)0ULL);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1525_, v_cs_1533_, v_sz_1536_, v___x_1537_, v___x_1535_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1553_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1553_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1553_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_fst_1543_; 
v_fst_1543_ = lean_ctor_get(v_a_1539_, 0);
if (lean_obj_tag(v_fst_1543_) == 0)
{
lean_object* v_snd_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v_snd_1544_ = lean_ctor_get(v_a_1539_, 1);
lean_inc(v_snd_1544_);
lean_dec(v_a_1539_);
v___x_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_snd_1544_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1545_);
v___x_1547_ = v___x_1541_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1551_; 
lean_inc_ref(v_fst_1543_);
lean_dec(v_a_1539_);
v_val_1549_ = lean_ctor_get(v_fst_1543_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_fst_1543_, 1);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_val_1549_);
v___x_1551_ = v___x_1541_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_val_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_a_1554_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1538_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1538_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_vs_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; size_t v_sz_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v_vs_1562_ = lean_ctor_get(v_n_1526_, 0);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v_b_1527_);
v_sz_1565_ = lean_array_size(v_vs_1562_);
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_1562_, v_sz_1565_, v___x_1566_, v___x_1564_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1582_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1582_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1582_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_fst_1572_; 
v_fst_1572_ = lean_ctor_get(v_a_1568_, 0);
if (lean_obj_tag(v_fst_1572_) == 0)
{
lean_object* v_snd_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v_snd_1573_ = lean_ctor_get(v_a_1568_, 1);
lean_inc(v_snd_1573_);
lean_dec(v_a_1568_);
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_snd_1573_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1574_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_object* v_val_1578_; lean_object* v___x_1580_; 
lean_inc_ref(v_fst_1572_);
lean_dec(v_a_1568_);
v_val_1578_ = lean_ctor_get(v_fst_1572_, 0);
lean_inc(v_val_1578_);
lean_dec_ref_known(v_fst_1572_, 1);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_val_1578_);
v___x_1580_ = v___x_1570_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_val_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_a_1583_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1567_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1567_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object* v_init_1591_, lean_object* v_as_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_b_1595_);
return v___x_1602_;
}
else
{
lean_object* v_snd_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1637_; 
v_snd_1603_ = lean_ctor_get(v_b_1595_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_b_1595_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_b_1595_, 0);
lean_dec(v_unused_1638_);
v___x_1605_ = v_b_1595_;
v_isShared_1606_ = v_isSharedCheck_1637_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_snd_1603_);
lean_dec(v_b_1595_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1637_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_a_1607_; lean_object* v___x_1608_; 
v_a_1607_ = lean_array_uget_borrowed(v_as_1592_, v_i_1594_);
lean_inc(v_snd_1603_);
v___x_1608_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1591_, v_a_1607_, v_snd_1603_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1628_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1628_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1628_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
if (lean_obj_tag(v_a_1609_) == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_a_1609_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1613_);
v___x_1615_ = v___x_1605_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_snd_1603_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1617_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1615_);
v___x_1617_ = v___x_1611_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_del_object(v___x_1611_);
lean_dec(v_snd_1603_);
v_a_1620_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v_a_1609_, 1);
v___x_1621_ = lean_box(0);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v_a_1620_);
lean_ctor_set(v___x_1605_, 0, v___x_1621_);
v___x_1623_ = v___x_1605_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_a_1620_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
size_t v___x_1624_; size_t v___x_1625_; 
v___x_1624_ = ((size_t)1ULL);
v___x_1625_ = lean_usize_add(v_i_1594_, v___x_1624_);
v_i_1594_ = v___x_1625_;
v_b_1595_ = v___x_1623_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_del_object(v___x_1605_);
lean_dec(v_snd_1603_);
v_a_1629_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1608_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1608_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1639_, lean_object* v_as_1640_, lean_object* v_sz_1641_, lean_object* v_i_1642_, lean_object* v_b_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
size_t v_sz_boxed_1649_; size_t v_i_boxed_1650_; lean_object* v_res_1651_; 
v_sz_boxed_1649_ = lean_unbox_usize(v_sz_1641_);
lean_dec(v_sz_1641_);
v_i_boxed_1650_ = lean_unbox_usize(v_i_1642_);
lean_dec(v_i_1642_);
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1639_, v_as_1640_, v_sz_boxed_1649_, v_i_boxed_1650_, v_b_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_as_1640_);
lean_dec(v_init_1639_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object* v_init_1652_, lean_object* v_n_1653_, lean_object* v_b_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1652_, v_n_1653_, v_b_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v_n_1653_);
lean_dec(v_init_1652_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1661_, size_t v_sz_1662_, size_t v_i_1663_, lean_object* v_b_1664_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1663_, v_sz_1662_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_b_1664_);
return v___x_1667_;
}
else
{
lean_object* v_snd_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1686_; 
v_snd_1668_ = lean_ctor_get(v_b_1664_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_b_1664_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v_b_1664_, 0);
lean_dec(v_unused_1687_);
v___x_1670_ = v_b_1664_;
v_isShared_1671_ = v_isSharedCheck_1686_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snd_1668_);
lean_dec(v_b_1664_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1686_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v_a_1674_; lean_object* v_a_1681_; 
v___x_1672_ = lean_box(0);
v_a_1681_ = lean_array_uget_borrowed(v_as_1661_, v_i_1663_);
if (lean_obj_tag(v_a_1681_) == 0)
{
v_a_1674_ = v_snd_1668_;
goto v___jp_1673_;
}
else
{
lean_object* v_val_1682_; uint8_t v___x_1683_; 
v_val_1682_ = lean_ctor_get(v_a_1681_, 0);
v___x_1683_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1682_);
if (v___x_1683_ == 0)
{
v_a_1674_ = v_snd_1668_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = l_Lean_LocalDecl_fvarId(v_val_1682_);
v___x_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v_snd_1668_);
v_a_1674_ = v___x_1685_;
goto v___jp_1673_;
}
}
v___jp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v_a_1674_);
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1676_ = v___x_1670_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_a_1674_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
size_t v___x_1677_; size_t v___x_1678_; 
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1663_, v___x_1677_);
v_i_1663_ = v___x_1678_;
v_b_1664_ = v___x_1676_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1688_, lean_object* v_sz_1689_, lean_object* v_i_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_){
_start:
{
size_t v_sz_boxed_1693_; size_t v_i_boxed_1694_; lean_object* v_res_1695_; 
v_sz_boxed_1693_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1694_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1688_, v_sz_boxed_1693_, v_i_boxed_1694_, v_b_1691_);
lean_dec_ref(v_as_1688_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(lean_object* v_as_1696_, size_t v_sz_1697_, size_t v_i_1698_, lean_object* v_b_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1698_, v_sz_1697_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_b_1699_);
return v___x_1706_;
}
else
{
lean_object* v_snd_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1725_; 
v_snd_1707_ = lean_ctor_get(v_b_1699_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_b_1699_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v_b_1699_, 0);
lean_dec(v_unused_1726_);
v___x_1709_ = v_b_1699_;
v_isShared_1710_ = v_isSharedCheck_1725_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_snd_1707_);
lean_dec(v_b_1699_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1725_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v_a_1713_; lean_object* v_a_1720_; 
v___x_1711_ = lean_box(0);
v_a_1720_ = lean_array_uget_borrowed(v_as_1696_, v_i_1698_);
if (lean_obj_tag(v_a_1720_) == 0)
{
v_a_1713_ = v_snd_1707_;
goto v___jp_1712_;
}
else
{
lean_object* v_val_1721_; uint8_t v___x_1722_; 
v_val_1721_ = lean_ctor_get(v_a_1720_, 0);
v___x_1722_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1721_);
if (v___x_1722_ == 0)
{
v_a_1713_ = v_snd_1707_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = l_Lean_LocalDecl_fvarId(v_val_1721_);
v___x_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v_snd_1707_);
v_a_1713_ = v___x_1724_;
goto v___jp_1712_;
}
}
v___jp_1712_:
{
lean_object* v___x_1715_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v_a_1713_);
lean_ctor_set(v___x_1709_, 0, v___x_1711_);
v___x_1715_ = v___x_1709_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_a_1713_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
size_t v___x_1716_; size_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_add(v_i_1698_, v___x_1716_);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1696_, v_sz_1697_, v___x_1717_, v___x_1715_);
return v___x_1718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(lean_object* v_as_1727_, lean_object* v_sz_1728_, lean_object* v_i_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
size_t v_sz_boxed_1736_; size_t v_i_boxed_1737_; lean_object* v_res_1738_; 
v_sz_boxed_1736_ = lean_unbox_usize(v_sz_1728_);
lean_dec(v_sz_1728_);
v_i_boxed_1737_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_1727_, v_sz_boxed_1736_, v_i_boxed_1737_, v_b_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v_as_1727_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(lean_object* v_t_1739_, lean_object* v_init_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_root_1746_; lean_object* v_tail_1747_; lean_object* v___x_1748_; 
v_root_1746_ = lean_ctor_get(v_t_1739_, 0);
v_tail_1747_ = lean_ctor_get(v_t_1739_, 1);
lean_inc(v_init_1740_);
v___x_1748_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1740_, v_root_1746_, v_init_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v_init_1740_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1785_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1785_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1785_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
if (lean_obj_tag(v_a_1749_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; 
v_a_1753_ = lean_ctor_get(v_a_1749_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v_a_1749_, 1);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v_a_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; size_t v_sz_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
lean_del_object(v___x_1751_);
v_a_1757_ = lean_ctor_get(v_a_1749_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v_a_1749_, 1);
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v_a_1757_);
v_sz_1760_ = lean_array_size(v_tail_1747_);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_1747_, v_sz_1760_, v___x_1761_, v___x_1759_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1776_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_fst_1767_; 
v_fst_1767_ = lean_ctor_get(v_a_1763_, 0);
if (lean_obj_tag(v_fst_1767_) == 0)
{
lean_object* v_snd_1768_; lean_object* v___x_1770_; 
v_snd_1768_ = lean_ctor_get(v_a_1763_, 1);
lean_inc(v_snd_1768_);
lean_dec(v_a_1763_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v_snd_1768_);
v___x_1770_ = v___x_1765_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_snd_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1774_; 
lean_inc_ref(v_fst_1767_);
lean_dec(v_a_1763_);
v_val_1772_ = lean_ctor_get(v_fst_1767_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v_fst_1767_, 1);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v_val_1772_);
v___x_1774_ = v___x_1765_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_val_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1762_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1762_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1748_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1748_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(lean_object* v_t_1794_, lean_object* v_init_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_t_1794_, v_init_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_t_1794_);
return v_res_1801_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(lean_object* v_as_x27_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
if (lean_obj_tag(v_as_x27_1811_) == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_b_1812_);
return v___x_1818_;
}
else
{
lean_object* v_head_1819_; lean_object* v_tail_1820_; lean_object* v___x_1821_; 
v_head_1819_ = lean_ctor_get(v_as_x27_1811_, 0);
v_tail_1820_ = lean_ctor_get(v_as_x27_1811_, 1);
lean_inc(v_head_1819_);
lean_inc(v_b_1812_);
v___x_1821_ = l_Lean_MVarId_clear(v_b_1812_, v_head_1819_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; 
lean_dec(v_b_1812_);
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v_as_x27_1811_ = v_tail_1820_;
v_b_1812_ = v_a_1822_;
goto _start;
}
else
{
lean_object* v_a_1824_; uint8_t v___y_1826_; uint8_t v___x_1867_; 
v_a_1824_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1824_);
v___x_1867_ = l_Lean_Exception_isInterrupt(v_a_1824_);
if (v___x_1867_ == 0)
{
uint8_t v___x_1868_; 
v___x_1868_ = l_Lean_Exception_isRuntime(v_a_1824_);
v___y_1826_ = v___x_1868_;
goto v___jp_1825_;
}
else
{
lean_dec(v_a_1824_);
v___y_1826_ = v___x_1867_;
goto v___jp_1825_;
}
v___jp_1825_:
{
if (v___y_1826_ == 0)
{
lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1865_; 
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1821_, 0);
lean_dec(v_unused_1866_);
v___x_1828_ = v___x_1821_;
v_isShared_1829_ = v_isSharedCheck_1865_;
goto v_resetjp_1827_;
}
else
{
lean_dec(v___x_1821_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1865_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; 
lean_inc(v_head_1819_);
v___x_1830_ = l_Lean_FVarId_getDecl___redArg(v_head_1819_, v___y_1813_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; uint8_t v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l_Lean_LocalDecl_isAuxDecl(v_a_1831_);
if (v___x_1832_ == 0)
{
lean_dec(v_a_1831_);
lean_del_object(v___x_1828_);
v_as_x27_1811_ = v_tail_1820_;
goto _start;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1834_ = l_Lean_LocalDecl_userName(v_a_1831_);
lean_dec(v_a_1831_);
v___x_1835_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_1836_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
v___x_1837_ = l_Lean_MessageData_ofName(v___x_1834_);
lean_inc_ref(v___x_1837_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1837_);
v___x_1842_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1843_);
v___x_1845_ = v___x_1828_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; 
lean_inc(v_b_1812_);
v___x_1846_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1835_, v_b_1812_, v___x_1845_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_dec_ref_known(v___x_1846_, 1);
v_as_x27_1811_ = v_tail_1820_;
goto _start;
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_b_1812_);
v_a_1848_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1846_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1846_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_del_object(v___x_1828_);
lean_dec(v_b_1812_);
v_a_1857_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1830_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1830_);
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
else
{
lean_dec(v_b_1812_);
return v___x_1821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(lean_object* v_as_x27_1869_, lean_object* v_b_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1869_, v_b_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v_as_x27_1869_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0(lean_object* v_mvarId_1877_, lean_object* v___x_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
lean_inc(v_mvarId_1877_);
v___x_1884_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1877_, v___x_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_lctx_1885_; lean_object* v_decls_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec_ref_known(v___x_1884_, 1);
v_lctx_1885_ = lean_ctor_get(v___y_1879_, 2);
v_decls_1886_ = lean_ctor_get(v_lctx_1885_, 1);
v___x_1887_ = lean_box(0);
v___x_1888_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_decls_1886_, v___x_1887_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1898_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
uint8_t v___x_1893_; 
v___x_1893_ = l_List_isEmpty___redArg(v_a_1889_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
lean_del_object(v___x_1891_);
v___x_1894_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_a_1889_, v_mvarId_1877_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v_a_1889_);
return v___x_1894_;
}
else
{
lean_object* v___x_1896_; 
lean_dec(v_a_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_mvarId_1877_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_mvarId_1877_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_mvarId_1877_);
v_a_1899_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1888_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1888_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_mvarId_1877_);
v_a_1907_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1884_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1884_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0___boxed(lean_object* v_mvarId_1915_, lean_object* v___x_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_MVarId_clearImplDetails___lam__0(v_mvarId_1915_, v___x_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails(lean_object* v_mvarId_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((lean_object*)(l_Lean_MVarId_clearImplDetails___closed__1));
lean_inc(v_mvarId_1927_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearImplDetails___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1934_, 0, v_mvarId_1927_);
lean_closure_set(v___f_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1927_, v___f_1934_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___boxed(lean_object* v_mvarId_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_MVarId_clearImplDetails(v_mvarId_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(lean_object* v_as_1943_, lean_object* v_as_x27_1944_, lean_object* v_b_1945_, lean_object* v_a_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1944_, v_b_1945_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___boxed(lean_object* v_as_1953_, lean_object* v_as_x27_1954_, lean_object* v_b_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(v_as_1953_, v_as_x27_1954_, v_b_1955_, v_a_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v_as_x27_1954_);
lean_dec(v_as_1953_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(lean_object* v_as_1963_, size_t v_sz_1964_, size_t v_i_1965_, lean_object* v_b_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1963_, v_sz_1964_, v_i_1965_, v_b_1966_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1973_, lean_object* v_sz_1974_, lean_object* v_i_1975_, lean_object* v_b_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
size_t v_sz_boxed_1982_; size_t v_i_boxed_1983_; lean_object* v_res_1984_; 
v_sz_boxed_1982_ = lean_unbox_usize(v_sz_1974_);
lean_dec(v_sz_1974_);
v_i_boxed_1983_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_res_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_1973_, v_sz_boxed_1982_, v_i_boxed_1983_, v_b_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec_ref(v_as_1973_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1985_, size_t v_sz_1986_, size_t v_i_1987_, lean_object* v_b_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1985_, v_sz_1986_, v_i_1987_, v_b_1988_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1995_, lean_object* v_sz_1996_, lean_object* v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
size_t v_sz_boxed_2004_; size_t v_i_boxed_2005_; lean_object* v_res_2006_; 
v_sz_boxed_2004_ = lean_unbox_usize(v_sz_1996_);
lean_dec(v_sz_1996_);
v_i_boxed_2005_ = lean_unbox_usize(v_i_1997_);
lean_dec(v_i_1997_);
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_1995_, v_sz_boxed_2004_, v_i_boxed_2005_, v_b_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v_as_1995_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object* v_e_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
switch(lean_obj_tag(v_e_2007_))
{
case 8:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_e_2007_);
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
return v___x_2012_;
}
case 6:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_e_2007_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
case 10:
{
lean_object* v_expr_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_expr_2015_ = lean_ctor_get(v_e_2007_, 1);
lean_inc_ref(v_expr_2015_);
lean_dec_ref_known(v_e_2007_, 2);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_expr_2015_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
default: 
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_e_2007_);
v___x_2019_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object* v_e_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object* v_e_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_e_2026_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object* v_e_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_object* v_00_u03b1_2037_, lean_object* v_x_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_apply_1(v_x_2038_, lean_box(0));
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(v_00_u03b1_2044_, v_x_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_m_2050_, lean_object* v_query_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_, lean_object* v_x_2054_){
_start:
{
lean_object* v_zero_2055_; uint8_t v_isZero_2056_; 
v_zero_2055_ = lean_unsigned_to_nat(0u);
v_isZero_2056_ = lean_nat_dec_eq(v_x_2053_, v_zero_2055_);
if (v_isZero_2056_ == 1)
{
lean_dec(v_x_2054_);
lean_dec(v_x_2053_);
if (lean_obj_tag(v_x_2052_) == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_box(2);
return v___x_2057_;
}
else
{
lean_object* v_val_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_val_2058_ = lean_ctor_get(v_x_2052_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_x_2052_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v_x_2052_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_val_2058_);
lean_dec(v_x_2052_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_val_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_keyArray_2066_; lean_object* v_valueArray_2067_; lean_object* v___x_2068_; uint8_t v_isSome_2069_; 
v_keyArray_2066_ = lean_ctor_get(v_m_2050_, 1);
v_valueArray_2067_ = lean_ctor_get(v_m_2050_, 2);
v___x_2068_ = lean_array_fget_borrowed(v_keyArray_2066_, v_x_2054_);
v_isSome_2069_ = lean_noption_is_some(v___x_2068_);
if (v_isSome_2069_ == 0)
{
lean_dec(v_x_2053_);
if (lean_obj_tag(v_x_2052_) == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_x_2054_);
return v___x_2070_;
}
else
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_x_2054_);
v_val_2071_ = lean_ctor_get(v_x_2052_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_x_2052_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v_x_2052_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v_x_2052_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_val_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_one_2079_; lean_object* v_n_2080_; lean_object* v___y_2082_; 
v_one_2079_ = lean_unsigned_to_nat(1u);
v_n_2080_ = lean_nat_sub(v_x_2053_, v_one_2079_);
lean_dec(v_x_2053_);
if (v_isSome_2069_ == 0)
{
goto v___jp_2088_;
}
else
{
lean_object* v___x_2090_; uint8_t v_isSome_2091_; 
v___x_2090_ = lean_array_fget_borrowed(v_valueArray_2067_, v_x_2054_);
v_isSome_2091_ = lean_noption_is_some(v___x_2090_);
if (v_isSome_2091_ == 0)
{
goto v___jp_2088_;
}
else
{
lean_object* v_val_2092_; uint8_t v___x_2093_; 
lean_inc(v___x_2068_);
v_val_2092_ = lean_noption_get(v___x_2068_);
v___x_2093_ = l_Lean_ExprStructEq_beq(v_val_2092_, v_query_2051_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
lean_dec(v_val_2092_);
v___x_2094_ = lean_array_get_size(v_keyArray_2066_);
v___x_2095_ = lean_nat_add(v_x_2054_, v_one_2079_);
lean_dec(v_x_2054_);
v___x_2096_ = lean_nat_dec_lt(v___x_2095_, v___x_2094_);
if (v___x_2096_ == 0)
{
lean_dec(v___x_2095_);
v_x_2053_ = v_n_2080_;
v_x_2054_ = v_zero_2055_;
goto _start;
}
else
{
v_x_2053_ = v_n_2080_;
v_x_2054_ = v___x_2095_;
goto _start;
}
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2100_; 
lean_dec(v_n_2080_);
lean_dec(v_x_2052_);
lean_inc(v___x_2090_);
v_val_2099_ = lean_noption_get(v___x_2090_);
v___x_2100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2100_, 0, v_x_2054_);
lean_ctor_set(v___x_2100_, 1, v_val_2092_);
lean_ctor_set(v___x_2100_, 2, v_val_2099_);
return v___x_2100_;
}
}
}
v___jp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = lean_array_get_size(v_keyArray_2066_);
v___x_2084_ = lean_nat_add(v_x_2054_, v_one_2079_);
lean_dec(v_x_2054_);
v___x_2085_ = lean_nat_dec_lt(v___x_2084_, v___x_2083_);
if (v___x_2085_ == 0)
{
lean_dec(v___x_2084_);
v_x_2052_ = v___y_2082_;
v_x_2053_ = v_n_2080_;
v_x_2054_ = v_zero_2055_;
goto _start;
}
else
{
v_x_2052_ = v___y_2082_;
v_x_2053_ = v_n_2080_;
v_x_2054_ = v___x_2084_;
goto _start;
}
}
v___jp_2088_:
{
if (lean_obj_tag(v_x_2052_) == 0)
{
lean_object* v___x_2089_; 
lean_inc(v_x_2054_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_x_2054_);
v___y_2082_ = v___x_2089_;
goto v___jp_2081_;
}
else
{
v___y_2082_ = v_x_2052_;
goto v___jp_2081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_m_2101_, lean_object* v_query_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_m_2101_, v_query_2102_, v_x_2103_, v_x_2104_, v_x_2105_);
lean_dec_ref(v_query_2102_);
lean_dec_ref(v_m_2101_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object* v_m_2107_, lean_object* v_query_2108_){
_start:
{
lean_object* v_keyArray_2109_; lean_object* v___x_2110_; uint64_t v___x_2111_; uint64_t v___x_2112_; uint64_t v___x_2113_; uint64_t v_fold_2114_; uint64_t v___x_2115_; uint64_t v___x_2116_; uint64_t v___x_2117_; size_t v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_keyArray_2109_ = lean_ctor_get(v_m_2107_, 1);
v___x_2110_ = lean_array_get_size(v_keyArray_2109_);
v___x_2111_ = l_Lean_ExprStructEq_hash(v_query_2108_);
v___x_2112_ = 32ULL;
v___x_2113_ = lean_uint64_shift_right(v___x_2111_, v___x_2112_);
v_fold_2114_ = lean_uint64_xor(v___x_2111_, v___x_2113_);
v___x_2115_ = 16ULL;
v___x_2116_ = lean_uint64_shift_right(v_fold_2114_, v___x_2115_);
v___x_2117_ = lean_uint64_xor(v_fold_2114_, v___x_2116_);
v___x_2118_ = lean_uint64_to_usize(v___x_2117_);
v___x_2119_ = lean_usize_of_nat(v___x_2110_);
v___x_2120_ = ((size_t)1ULL);
v___x_2121_ = lean_usize_sub(v___x_2119_, v___x_2120_);
v___x_2122_ = lean_usize_land(v___x_2118_, v___x_2121_);
v___x_2123_ = lean_usize_to_nat(v___x_2122_);
v___x_2124_ = lean_box(0);
v___x_2125_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_m_2107_, v_query_2108_, v___x_2124_, v___x_2110_, v___x_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_m_2126_, lean_object* v_query_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2126_, v_query_2127_);
lean_dec_ref(v_query_2127_);
lean_dec_ref(v_m_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_m_2129_, lean_object* v_query_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2129_, v_query_2130_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_index_2132_; lean_object* v_key_2133_; lean_object* v_value_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_index_2132_ = lean_ctor_get(v___x_2131_, 0);
v_key_2133_ = lean_ctor_get(v___x_2131_, 1);
v_value_2134_ = lean_ctor_get(v___x_2131_, 2);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2131_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_value_2134_);
lean_inc(v_key_2133_);
lean_inc(v_index_2132_);
lean_dec(v___x_2131_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_index_2132_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_key_2133_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_value_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
else
{
lean_object* v___x_2142_; 
lean_dec(v___x_2131_);
v___x_2142_ = lean_box(1);
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_m_2143_, lean_object* v_query_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_m_2143_, v_query_2144_);
lean_dec_ref(v_query_2144_);
lean_dec_ref(v_m_2143_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_m_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_value_2149_; lean_object* v___x_2150_; 
v_value_2149_ = lean_ctor_get(v___x_2148_, 2);
lean_inc(v_value_2149_);
lean_dec_ref_known(v___x_2148_, 3);
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_value_2149_);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; 
v___x_2151_ = lean_box(0);
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2152_, v_a_2153_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_m_2152_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_apply_1(v_x_2156_, lean_box(0));
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_x_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_2162_, v_x_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2167_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = l_Lean_maxRecDepthErrorMessage;
v___x_2174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_2176_ = l_Lean_MessageData_ofFormat(v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_2178_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_2179_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_2180_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_ref_2180_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2185_);
return v_res_2187_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_box(0);
v___x_2189_ = l_Lean_interruptExceptionId;
v___x_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___y_2202_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; uint8_t v___y_2221_; lean_object* v___y_2222_; uint8_t v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v_fileName_2232_; lean_object* v_fileMap_2233_; lean_object* v_options_2234_; lean_object* v_currRecDepth_2235_; lean_object* v_maxRecDepth_2236_; lean_object* v_ref_2237_; lean_object* v_currNamespace_2238_; lean_object* v_openDecls_2239_; lean_object* v_initHeartbeats_2240_; lean_object* v_maxHeartbeats_2241_; lean_object* v_quotContext_2242_; lean_object* v_currMacroScope_2243_; uint8_t v_diag_2244_; lean_object* v_cancelTk_x3f_2245_; uint8_t v_suppressElabErrors_2246_; lean_object* v_inheritedTraceOptions_2247_; 
v_fileName_2232_ = lean_ctor_get(v___y_2198_, 0);
v_fileMap_2233_ = lean_ctor_get(v___y_2198_, 1);
v_options_2234_ = lean_ctor_get(v___y_2198_, 2);
v_currRecDepth_2235_ = lean_ctor_get(v___y_2198_, 3);
v_maxRecDepth_2236_ = lean_ctor_get(v___y_2198_, 4);
v_ref_2237_ = lean_ctor_get(v___y_2198_, 5);
v_currNamespace_2238_ = lean_ctor_get(v___y_2198_, 6);
v_openDecls_2239_ = lean_ctor_get(v___y_2198_, 7);
v_initHeartbeats_2240_ = lean_ctor_get(v___y_2198_, 8);
v_maxHeartbeats_2241_ = lean_ctor_get(v___y_2198_, 9);
v_quotContext_2242_ = lean_ctor_get(v___y_2198_, 10);
v_currMacroScope_2243_ = lean_ctor_get(v___y_2198_, 11);
v_diag_2244_ = lean_ctor_get_uint8(v___y_2198_, sizeof(void*)*14);
v_cancelTk_x3f_2245_ = lean_ctor_get(v___y_2198_, 12);
v_suppressElabErrors_2246_ = lean_ctor_get_uint8(v___y_2198_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2247_ = lean_ctor_get(v___y_2198_, 13);
if (lean_obj_tag(v_cancelTk_x3f_2245_) == 1)
{
lean_object* v_val_2253_; uint8_t v___x_2254_; 
v_val_2253_ = lean_ctor_get(v_cancelTk_x3f_2245_, 0);
v___x_2254_ = l_IO_CancelToken_isSet(v_val_2253_);
if (v___x_2254_ == 0)
{
goto v___jp_2248_;
}
else
{
lean_object* v___x_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_x_2196_);
v___x_2255_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
goto v___jp_2248_;
}
v___jp_2201_:
{
if (lean_obj_tag(v___y_2202_) == 0)
{
return v___y_2202_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_a_2203_ = lean_ctor_get(v___y_2202_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___y_2202_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___y_2202_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___y_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
v___jp_2211_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2228_ = lean_unsigned_to_nat(1u);
v___x_2229_ = lean_nat_add(v___y_2227_, v___x_2228_);
lean_inc_ref(v___y_2214_);
lean_inc(v___y_2226_);
lean_inc(v___y_2213_);
lean_inc(v___y_2225_);
lean_inc(v___y_2219_);
lean_inc(v___y_2224_);
lean_inc(v___y_2212_);
lean_inc(v___y_2217_);
lean_inc(v___y_2220_);
lean_inc_ref(v___y_2218_);
lean_inc_ref(v___y_2215_);
lean_inc_ref(v___y_2222_);
v___x_2230_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2230_, 0, v___y_2222_);
lean_ctor_set(v___x_2230_, 1, v___y_2215_);
lean_ctor_set(v___x_2230_, 2, v___y_2218_);
lean_ctor_set(v___x_2230_, 3, v___x_2229_);
lean_ctor_set(v___x_2230_, 4, v___y_2220_);
lean_ctor_set(v___x_2230_, 5, v___y_2216_);
lean_ctor_set(v___x_2230_, 6, v___y_2217_);
lean_ctor_set(v___x_2230_, 7, v___y_2212_);
lean_ctor_set(v___x_2230_, 8, v___y_2224_);
lean_ctor_set(v___x_2230_, 9, v___y_2219_);
lean_ctor_set(v___x_2230_, 10, v___y_2225_);
lean_ctor_set(v___x_2230_, 11, v___y_2213_);
lean_ctor_set(v___x_2230_, 12, v___y_2226_);
lean_ctor_set(v___x_2230_, 13, v___y_2214_);
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*14, v___y_2223_);
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*14 + 1, v___y_2221_);
lean_inc(v___y_2199_);
lean_inc(v___y_2197_);
v___x_2231_ = lean_apply_4(v_x_2196_, v___y_2197_, v___x_2230_, v___y_2199_, lean_box(0));
v___y_2202_ = v___x_2231_;
goto v___jp_2201_;
}
v___jp_2248_:
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = lean_nat_dec_eq(v_maxRecDepth_2236_, v___x_2249_);
if (v___x_2250_ == 0)
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_nat_dec_eq(v_currRecDepth_2235_, v_maxRecDepth_2236_);
if (v___x_2251_ == 0)
{
lean_inc(v_ref_2237_);
v___y_2212_ = v_openDecls_2239_;
v___y_2213_ = v_currMacroScope_2243_;
v___y_2214_ = v_inheritedTraceOptions_2247_;
v___y_2215_ = v_fileMap_2233_;
v___y_2216_ = v_ref_2237_;
v___y_2217_ = v_currNamespace_2238_;
v___y_2218_ = v_options_2234_;
v___y_2219_ = v_maxHeartbeats_2241_;
v___y_2220_ = v_maxRecDepth_2236_;
v___y_2221_ = v_suppressElabErrors_2246_;
v___y_2222_ = v_fileName_2232_;
v___y_2223_ = v_diag_2244_;
v___y_2224_ = v_initHeartbeats_2240_;
v___y_2225_ = v_quotContext_2242_;
v___y_2226_ = v_cancelTk_x3f_2245_;
v___y_2227_ = v_currRecDepth_2235_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2252_; 
lean_dec_ref(v_x_2196_);
lean_inc(v_ref_2237_);
v___x_2252_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2237_);
v___y_2202_ = v___x_2252_;
goto v___jp_2201_;
}
}
else
{
lean_inc(v_ref_2237_);
v___y_2212_ = v_openDecls_2239_;
v___y_2213_ = v_currMacroScope_2243_;
v___y_2214_ = v_inheritedTraceOptions_2247_;
v___y_2215_ = v_fileMap_2233_;
v___y_2216_ = v_ref_2237_;
v___y_2217_ = v_currNamespace_2238_;
v___y_2218_ = v_options_2234_;
v___y_2219_ = v_maxHeartbeats_2241_;
v___y_2220_ = v_maxRecDepth_2236_;
v___y_2221_ = v_suppressElabErrors_2246_;
v___y_2222_ = v_fileName_2232_;
v___y_2223_ = v_diag_2244_;
v___y_2224_ = v_initHeartbeats_2240_;
v___y_2225_ = v_quotContext_2242_;
v___y_2226_ = v_cancelTk_x3f_2245_;
v___y_2227_ = v_currRecDepth_2235_;
goto v___jp_2211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object* v_b_2270_, lean_object* v_acc_2271_, lean_object* v_i_2272_){
_start:
{
lean_object* v___y_2274_; lean_object* v_keyArray_2282_; lean_object* v_valueArray_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_keyArray_2282_ = lean_ctor_get(v_b_2270_, 1);
v_valueArray_2283_ = lean_ctor_get(v_b_2270_, 2);
v___x_2284_ = lean_array_get_size(v_keyArray_2282_);
v___x_2285_ = lean_nat_dec_lt(v_i_2272_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_dec(v_i_2272_);
return v_acc_2271_;
}
else
{
lean_object* v___x_2286_; uint8_t v_isSome_2287_; 
v___x_2286_ = lean_array_fget_borrowed(v_keyArray_2282_, v_i_2272_);
v_isSome_2287_ = lean_noption_is_some(v___x_2286_);
if (v_isSome_2287_ == 0)
{
goto v___jp_2278_;
}
else
{
lean_object* v___x_2288_; uint8_t v_isSome_2289_; 
v___x_2288_ = lean_array_fget_borrowed(v_valueArray_2283_, v_i_2272_);
v_isSome_2289_ = lean_noption_is_some(v___x_2288_);
if (v_isSome_2289_ == 0)
{
goto v___jp_2278_;
}
else
{
lean_object* v_val_2290_; lean_object* v_val_2291_; lean_object* v_i_2293_; lean_object* v___x_2298_; 
lean_inc(v___x_2286_);
v_val_2290_ = lean_noption_get(v___x_2286_);
lean_inc(v___x_2288_);
v_val_2291_ = lean_noption_get(v___x_2288_);
v___x_2298_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_acc_2271_, v_val_2290_);
switch(lean_obj_tag(v___x_2298_))
{
case 0:
{
lean_object* v_index_2299_; lean_object* v_size_2300_; lean_object* v___x_2301_; 
v_index_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_index_2299_);
lean_dec_ref_known(v___x_2298_, 3);
v_size_2300_ = lean_ctor_get(v_acc_2271_, 0);
lean_inc(v_size_2300_);
v___x_2301_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2271_, v_size_2300_, v_index_2299_, v_val_2290_, v_val_2291_);
lean_dec(v_index_2299_);
v___y_2274_ = v___x_2301_;
goto v___jp_2273_;
}
case 1:
{
lean_object* v_index_2302_; 
v_index_2302_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_index_2302_);
lean_dec_ref_known(v___x_2298_, 1);
v_i_2293_ = v_index_2302_;
goto v___jp_2292_;
}
default: 
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2271_, v___x_2303_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_index_2305_; 
v_index_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_index_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_i_2293_ = v_index_2305_;
goto v___jp_2292_;
}
else
{
lean_dec(v_val_2291_);
lean_dec(v_val_2290_);
v___y_2274_ = v_acc_2271_;
goto v___jp_2273_;
}
}
}
v___jp_2292_:
{
lean_object* v_size_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_size_2294_ = lean_ctor_get(v_acc_2271_, 0);
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_nat_add(v_size_2294_, v___x_2295_);
v___x_2297_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2271_, v___x_2296_, v_i_2293_, v_val_2290_, v_val_2291_);
lean_dec(v_i_2293_);
v___y_2274_ = v___x_2297_;
goto v___jp_2273_;
}
}
}
}
v___jp_2273_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = lean_nat_add(v_i_2272_, v___x_2275_);
lean_dec(v_i_2272_);
v_acc_2271_ = v___y_2274_;
v_i_2272_ = v___x_2276_;
goto _start;
}
v___jp_2278_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = lean_nat_add(v_i_2272_, v___x_2279_);
lean_dec(v_i_2272_);
v_i_2272_ = v___x_2280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object* v_b_2306_, lean_object* v_acc_2307_, lean_object* v_i_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_2306_, v_acc_2307_, v_i_2308_);
lean_dec_ref(v_b_2306_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___redArg(lean_object* v_init_2310_, lean_object* v_b_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_2311_, v_init_2310_, v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object* v_init_2314_, lean_object* v_b_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___redArg(v_init_2314_, v_b_2315_);
lean_dec_ref(v_b_2315_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg(lean_object* v_m_2317_){
_start:
{
lean_object* v_keyArray_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_cellCount_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_target_2325_; lean_object* v___x_2326_; 
v_keyArray_2318_ = lean_ctor_get(v_m_2317_, 1);
v___x_2319_ = lean_array_get_size(v_keyArray_2318_);
v___x_2320_ = lean_unsigned_to_nat(2u);
v_cellCount_2321_ = lean_nat_mul(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2321_);
v___x_2323_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2321_);
v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2321_);
v_target_2325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2325_, 0, v___x_2322_);
lean_ctor_set(v_target_2325_, 1, v___x_2323_);
lean_ctor_set(v_target_2325_, 2, v___x_2324_);
v___x_2326_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___redArg(v_target_2325_, v_m_2317_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_m_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg(v_m_2327_);
lean_dec_ref(v_m_2327_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object* v_a_2329_, lean_object* v_e_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___y_2336_; lean_object* v___y_2339_; lean_object* v_i_2340_; lean_object* v___y_2356_; lean_object* v_i_2357_; lean_object* v___y_2363_; lean_object* v___x_2372_; 
v___x_2333_ = lean_st_ref_take(v_a_2329_);
v___x_2334_ = lean_box(0);
v___x_2372_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2333_, v_e_2330_);
switch(lean_obj_tag(v___x_2372_))
{
case 0:
{
lean_object* v_index_2373_; lean_object* v_size_2374_; lean_object* v___x_2375_; 
v_index_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_index_2373_);
lean_dec_ref_known(v___x_2372_, 3);
v_size_2374_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_size_2374_);
v___x_2375_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2333_, v_size_2374_, v_index_2373_, v_e_2330_, v_a_2331_);
lean_dec(v_index_2373_);
v___y_2336_ = v___x_2375_;
goto v___jp_2335_;
}
case 1:
{
lean_object* v_index_2376_; lean_object* v_size_2377_; lean_object* v_keyArray_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_index_2376_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_index_2376_);
lean_dec_ref_known(v___x_2372_, 1);
v_size_2377_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_size_2377_);
v_keyArray_2378_ = lean_ctor_get(v___x_2333_, 1);
lean_inc_ref(v_keyArray_2378_);
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_nat_add(v_size_2377_, v___x_2379_);
lean_dec(v_size_2377_);
v___x_2381_ = lean_array_get_size(v_keyArray_2378_);
lean_dec_ref(v_keyArray_2378_);
v___x_2382_ = lean_nat_dec_lt(v___x_2380_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_dec(v___x_2380_);
lean_dec(v_index_2376_);
goto v___jp_2345_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2383_ = lean_unsigned_to_nat(4u);
v___x_2384_ = lean_nat_mul(v___x_2380_, v___x_2383_);
v___x_2385_ = lean_unsigned_to_nat(3u);
v___x_2386_ = lean_nat_mul(v___x_2381_, v___x_2385_);
v___x_2387_ = lean_nat_dec_le(v___x_2384_, v___x_2386_);
lean_dec(v___x_2386_);
lean_dec(v___x_2384_);
if (v___x_2387_ == 0)
{
lean_dec(v___x_2380_);
lean_dec(v_index_2376_);
goto v___jp_2345_;
}
else
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2333_, v___x_2380_, v_index_2376_, v_e_2330_, v_a_2331_);
lean_dec(v_index_2376_);
v___y_2336_ = v___x_2388_;
goto v___jp_2335_;
}
}
}
default: 
{
lean_object* v_size_2389_; lean_object* v_keyArray_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v_size_2389_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_size_2389_);
v_keyArray_2390_ = lean_ctor_get(v___x_2333_, 1);
lean_inc_ref(v_keyArray_2390_);
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = lean_nat_add(v_size_2389_, v___x_2391_);
lean_dec(v_size_2389_);
v___x_2393_ = lean_array_get_size(v_keyArray_2390_);
lean_dec_ref(v_keyArray_2390_);
v___x_2394_ = lean_nat_dec_lt(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
lean_dec(v___x_2392_);
v___x_2395_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg(v___x_2333_);
lean_dec(v___x_2333_);
v___y_2363_ = v___x_2395_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2396_ = lean_unsigned_to_nat(4u);
v___x_2397_ = lean_nat_mul(v___x_2392_, v___x_2396_);
lean_dec(v___x_2392_);
v___x_2398_ = lean_unsigned_to_nat(3u);
v___x_2399_ = lean_nat_mul(v___x_2393_, v___x_2398_);
v___x_2400_ = lean_nat_dec_le(v___x_2397_, v___x_2399_);
lean_dec(v___x_2399_);
lean_dec(v___x_2397_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg(v___x_2333_);
lean_dec(v___x_2333_);
v___y_2363_ = v___x_2401_;
goto v___jp_2362_;
}
else
{
v___y_2363_ = v___x_2333_;
goto v___jp_2362_;
}
}
}
}
v___jp_2335_:
{
lean_object* v___x_2337_; 
v___x_2337_ = lean_st_ref_put(v_a_2329_, v___y_2336_);
return v___x_2334_;
}
v___jp_2338_:
{
lean_object* v_size_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_size_2341_ = lean_ctor_get(v___y_2339_, 0);
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = lean_nat_add(v_size_2341_, v___x_2342_);
v___x_2344_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2339_, v___x_2343_, v_i_2340_, v_e_2330_, v_a_2331_);
lean_dec(v_i_2340_);
v___y_2336_ = v___x_2344_;
goto v___jp_2335_;
}
v___jp_2345_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg(v___x_2333_);
lean_dec(v___x_2333_);
v___x_2347_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2346_, v_e_2330_);
switch(lean_obj_tag(v___x_2347_))
{
case 0:
{
lean_object* v_index_2348_; lean_object* v_size_2349_; lean_object* v___x_2350_; 
v_index_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_index_2348_);
lean_dec_ref_known(v___x_2347_, 3);
v_size_2349_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_size_2349_);
v___x_2350_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2346_, v_size_2349_, v_index_2348_, v_e_2330_, v_a_2331_);
lean_dec(v_index_2348_);
v___y_2336_ = v___x_2350_;
goto v___jp_2335_;
}
case 1:
{
lean_object* v_index_2351_; 
v_index_2351_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_index_2351_);
lean_dec_ref_known(v___x_2347_, 1);
v___y_2339_ = v___x_2346_;
v_i_2340_ = v_index_2351_;
goto v___jp_2338_;
}
default: 
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2346_, v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_index_2354_; 
v_index_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_index_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___y_2339_ = v___x_2346_;
v_i_2340_ = v_index_2354_;
goto v___jp_2338_;
}
else
{
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_e_2330_);
v___y_2336_ = v___x_2346_;
goto v___jp_2335_;
}
}
}
}
v___jp_2355_:
{
lean_object* v_size_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_size_2358_ = lean_ctor_get(v___y_2356_, 0);
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_add(v_size_2358_, v___x_2359_);
v___x_2361_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2356_, v___x_2360_, v_i_2357_, v_e_2330_, v_a_2331_);
lean_dec(v_i_2357_);
v___y_2336_ = v___x_2361_;
goto v___jp_2335_;
}
v___jp_2362_:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___y_2363_, v_e_2330_);
switch(lean_obj_tag(v___x_2364_))
{
case 0:
{
lean_object* v_index_2365_; lean_object* v_size_2366_; lean_object* v___x_2367_; 
v_index_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_index_2365_);
lean_dec_ref_known(v___x_2364_, 3);
v_size_2366_ = lean_ctor_get(v___y_2363_, 0);
lean_inc(v_size_2366_);
v___x_2367_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2363_, v_size_2366_, v_index_2365_, v_e_2330_, v_a_2331_);
lean_dec(v_index_2365_);
v___y_2336_ = v___x_2367_;
goto v___jp_2335_;
}
case 1:
{
lean_object* v_index_2368_; 
v_index_2368_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_index_2368_);
lean_dec_ref_known(v___x_2364_, 1);
v___y_2356_ = v___y_2363_;
v_i_2357_ = v_index_2368_;
goto v___jp_2355_;
}
default: 
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2363_, v___x_2369_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_index_2371_; 
v_index_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_index_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v___y_2356_ = v___y_2363_;
v_i_2357_ = v_index_2371_;
goto v___jp_2355_;
}
else
{
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_e_2330_);
v___y_2336_ = v___y_2363_;
goto v___jp_2335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2402_, lean_object* v_e_2403_, lean_object* v_a_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2402_, v_e_2403_, v_a_2404_);
lean_dec(v_a_2402_);
return v_res_2406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2408_; lean_object* v_dummy_2409_; 
v___x_2408_ = lean_box(0);
v_dummy_2409_ = l_Lean_Expr_sort___override(v___x_2408_);
return v_dummy_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object* v_pre_2410_, lean_object* v_post_2411_, size_t v_sz_2412_, size_t v_i_2413_, lean_object* v_bs_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = lean_usize_dec_lt(v_i_2413_, v_sz_2412_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v_post_2411_);
lean_dec_ref(v_pre_2410_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_bs_2414_);
return v___x_2420_;
}
else
{
lean_object* v_v_2421_; lean_object* v___x_2422_; 
v_v_2421_ = lean_array_uget_borrowed(v_bs_2414_, v_i_2413_);
lean_inc(v_v_2421_);
lean_inc_ref(v_post_2411_);
lean_inc_ref(v_pre_2410_);
v___x_2422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2410_, v_post_2411_, v_v_2421_, v___y_2415_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; lean_object* v_bs_x27_2425_; size_t v___x_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = lean_unsigned_to_nat(0u);
v_bs_x27_2425_ = lean_array_uset(v_bs_2414_, v_i_2413_, v___x_2424_);
v___x_2426_ = ((size_t)1ULL);
v___x_2427_ = lean_usize_add(v_i_2413_, v___x_2426_);
v___x_2428_ = lean_array_uset(v_bs_x27_2425_, v_i_2413_, v_a_2423_);
v_i_2413_ = v___x_2427_;
v_bs_2414_ = v___x_2428_;
goto _start;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v_bs_2414_);
lean_dec_ref(v_post_2411_);
lean_dec_ref(v_pre_2410_);
v_a_2430_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2422_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2422_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object* v_pre_2438_, lean_object* v_post_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
if (lean_obj_tag(v_x_2440_) == 5)
{
lean_object* v_fn_2447_; lean_object* v_arg_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_fn_2447_ = lean_ctor_get(v_x_2440_, 0);
lean_inc_ref(v_fn_2447_);
v_arg_2448_ = lean_ctor_get(v_x_2440_, 1);
lean_inc_ref(v_arg_2448_);
lean_dec_ref_known(v_x_2440_, 2);
v___x_2449_ = lean_array_set(v_x_2441_, v_x_2442_, v_arg_2448_);
v___x_2450_ = lean_unsigned_to_nat(1u);
v___x_2451_ = lean_nat_sub(v_x_2442_, v___x_2450_);
lean_dec(v_x_2442_);
v_x_2440_ = v_fn_2447_;
v_x_2441_ = v___x_2449_;
v_x_2442_ = v___x_2451_;
goto _start;
}
else
{
lean_object* v___x_2453_; 
lean_dec(v_x_2442_);
lean_inc_ref(v_post_2439_);
lean_inc_ref(v_pre_2438_);
v___x_2453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2438_, v_post_2439_, v_x_2440_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; size_t v_sz_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v_sz_2455_ = lean_array_size(v_x_2441_);
v___x_2456_ = ((size_t)0ULL);
lean_inc_ref(v_post_2439_);
lean_inc_ref(v_pre_2438_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2438_, v_post_2439_, v_sz_2455_, v___x_2456_, v_x_2441_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = l_Lean_mkAppN(v_a_2454_, v_a_2458_);
lean_dec(v_a_2458_);
v___x_2460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2438_, v_post_2439_, v___x_2459_, v___y_2443_, v___y_2444_, v___y_2445_);
return v___x_2460_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2454_);
lean_dec_ref(v_post_2439_);
lean_dec_ref(v_pre_2438_);
v_a_2461_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2457_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2457_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_dec_ref(v_x_2441_);
lean_dec_ref(v_post_2439_);
lean_dec_ref(v_pre_2438_);
return v___x_2453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object* v___x_2469_, lean_object* v_pre_2470_, lean_object* v_e_2471_, lean_object* v_post_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___y_2478_; lean_object* v___y_2479_; uint8_t v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; uint8_t v___y_2485_; lean_object* v___y_2495_; uint8_t v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; uint8_t v___y_2500_; uint8_t v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; uint8_t v___y_2513_; lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Core_checkSystem(v___x_2469_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2521_; 
lean_dec_ref_known(v___x_2520_, 1);
lean_inc_ref(v_pre_2470_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc_ref(v_e_2471_);
v___x_2521_ = lean_apply_4(v_pre_2470_, v_e_2471_, v___y_2474_, v___y_2475_, lean_box(0));
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2611_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2611_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2611_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___y_2527_; 
switch(lean_obj_tag(v_a_2522_))
{
case 0:
{
lean_object* v_e_2601_; lean_object* v___x_2603_; 
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_e_2471_);
lean_dec_ref(v_pre_2470_);
v_e_2601_ = lean_ctor_get(v_a_2522_, 0);
lean_inc_ref(v_e_2601_);
lean_dec_ref_known(v_a_2522_, 1);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v_e_2601_);
v___x_2603_ = v___x_2524_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_e_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
case 1:
{
lean_object* v_e_2605_; lean_object* v___x_2606_; 
lean_del_object(v___x_2524_);
lean_dec_ref(v_e_2471_);
v_e_2605_ = lean_ctor_get(v_a_2522_, 0);
lean_inc_ref(v_e_2605_);
lean_dec_ref_known(v_a_2522_, 1);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2606_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_e_2605_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v_a_2607_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2608_;
}
else
{
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2606_;
}
}
default: 
{
lean_object* v_e_x3f_2609_; 
lean_del_object(v___x_2524_);
v_e_x3f_2609_ = lean_ctor_get(v_a_2522_, 0);
lean_inc(v_e_x3f_2609_);
lean_dec_ref_known(v_a_2522_, 1);
if (lean_obj_tag(v_e_x3f_2609_) == 0)
{
v___y_2527_ = v_e_2471_;
goto v___jp_2526_;
}
else
{
lean_object* v_val_2610_; 
lean_dec_ref(v_e_2471_);
v_val_2610_ = lean_ctor_get(v_e_x3f_2609_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v_e_x3f_2609_, 1);
v___y_2527_ = v_val_2610_;
goto v___jp_2526_;
}
}
}
v___jp_2526_:
{
switch(lean_obj_tag(v___y_2527_))
{
case 7:
{
lean_object* v_binderName_2528_; lean_object* v_binderType_2529_; lean_object* v_body_2530_; uint8_t v_binderInfo_2531_; lean_object* v___x_2532_; 
v_binderName_2528_ = lean_ctor_get(v___y_2527_, 0);
lean_inc(v_binderName_2528_);
v_binderType_2529_ = lean_ctor_get(v___y_2527_, 1);
v_body_2530_ = lean_ctor_get(v___y_2527_, 2);
v_binderInfo_2531_ = lean_ctor_get_uint8(v___y_2527_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2529_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_binderType_2529_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
lean_inc_ref(v_body_2530_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_body_2530_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; size_t v___x_2536_; size_t v___x_2537_; uint8_t v___x_2538_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = lean_ptr_addr(v_binderType_2529_);
v___x_2537_ = lean_ptr_addr(v_a_2533_);
v___x_2538_ = lean_usize_dec_eq(v___x_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
v___y_2508_ = v_binderInfo_2531_;
v___y_2509_ = v___y_2527_;
v___y_2510_ = v_a_2533_;
v___y_2511_ = v_a_2535_;
v___y_2512_ = v_binderName_2528_;
v___y_2513_ = v___x_2538_;
goto v___jp_2507_;
}
else
{
size_t v___x_2539_; size_t v___x_2540_; uint8_t v___x_2541_; 
v___x_2539_ = lean_ptr_addr(v_body_2530_);
v___x_2540_ = lean_ptr_addr(v_a_2535_);
v___x_2541_ = lean_usize_dec_eq(v___x_2539_, v___x_2540_);
v___y_2508_ = v_binderInfo_2531_;
v___y_2509_ = v___y_2527_;
v___y_2510_ = v_a_2533_;
v___y_2511_ = v_a_2535_;
v___y_2512_ = v_binderName_2528_;
v___y_2513_ = v___x_2541_;
goto v___jp_2507_;
}
}
else
{
lean_dec(v_a_2533_);
lean_dec_ref_known(v___y_2527_, 3);
lean_dec(v_binderName_2528_);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2534_;
}
}
else
{
lean_dec(v_binderName_2528_);
lean_dec_ref_known(v___y_2527_, 3);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2532_;
}
}
case 6:
{
lean_object* v_binderName_2542_; lean_object* v_binderType_2543_; lean_object* v_body_2544_; uint8_t v_binderInfo_2545_; lean_object* v___x_2546_; 
v_binderName_2542_ = lean_ctor_get(v___y_2527_, 0);
lean_inc(v_binderName_2542_);
v_binderType_2543_ = lean_ctor_get(v___y_2527_, 1);
v_body_2544_ = lean_ctor_get(v___y_2527_, 2);
v_binderInfo_2545_ = lean_ctor_get_uint8(v___y_2527_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2543_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2546_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_binderType_2543_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
lean_inc_ref(v_body_2544_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2548_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_body_2544_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; size_t v___x_2550_; size_t v___x_2551_; uint8_t v___x_2552_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = lean_ptr_addr(v_binderType_2543_);
v___x_2551_ = lean_ptr_addr(v_a_2547_);
v___x_2552_ = lean_usize_dec_eq(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
v___y_2495_ = v___y_2527_;
v___y_2496_ = v_binderInfo_2545_;
v___y_2497_ = v_a_2549_;
v___y_2498_ = v_binderName_2542_;
v___y_2499_ = v_a_2547_;
v___y_2500_ = v___x_2552_;
goto v___jp_2494_;
}
else
{
size_t v___x_2553_; size_t v___x_2554_; uint8_t v___x_2555_; 
v___x_2553_ = lean_ptr_addr(v_body_2544_);
v___x_2554_ = lean_ptr_addr(v_a_2549_);
v___x_2555_ = lean_usize_dec_eq(v___x_2553_, v___x_2554_);
v___y_2495_ = v___y_2527_;
v___y_2496_ = v_binderInfo_2545_;
v___y_2497_ = v_a_2549_;
v___y_2498_ = v_binderName_2542_;
v___y_2499_ = v_a_2547_;
v___y_2500_ = v___x_2555_;
goto v___jp_2494_;
}
}
else
{
lean_dec(v_a_2547_);
lean_dec_ref_known(v___y_2527_, 3);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2548_;
}
}
else
{
lean_dec_ref_known(v___y_2527_, 3);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2546_;
}
}
case 8:
{
lean_object* v_declName_2556_; lean_object* v_type_2557_; lean_object* v_value_2558_; lean_object* v_body_2559_; uint8_t v_nondep_2560_; lean_object* v___x_2561_; 
v_declName_2556_ = lean_ctor_get(v___y_2527_, 0);
lean_inc(v_declName_2556_);
v_type_2557_ = lean_ctor_get(v___y_2527_, 1);
v_value_2558_ = lean_ctor_get(v___y_2527_, 2);
v_body_2559_ = lean_ctor_get(v___y_2527_, 3);
lean_inc_ref(v_body_2559_);
v_nondep_2560_ = lean_ctor_get_uint8(v___y_2527_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2557_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_type_2557_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
lean_inc_ref(v_value_2558_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_value_2558_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
lean_inc_ref(v_body_2559_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_body_2559_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; size_t v___x_2567_; size_t v___x_2568_; uint8_t v___x_2569_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = lean_ptr_addr(v_type_2557_);
v___x_2568_ = lean_ptr_addr(v_a_2562_);
v___x_2569_ = lean_usize_dec_eq(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2478_ = v___y_2527_;
v___y_2479_ = v_a_2564_;
v___y_2480_ = v_nondep_2560_;
v___y_2481_ = v_declName_2556_;
v___y_2482_ = v_a_2562_;
v___y_2483_ = v_a_2566_;
v___y_2484_ = v_body_2559_;
v___y_2485_ = v___x_2569_;
goto v___jp_2477_;
}
else
{
size_t v___x_2570_; size_t v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = lean_ptr_addr(v_value_2558_);
v___x_2571_ = lean_ptr_addr(v_a_2564_);
v___x_2572_ = lean_usize_dec_eq(v___x_2570_, v___x_2571_);
v___y_2478_ = v___y_2527_;
v___y_2479_ = v_a_2564_;
v___y_2480_ = v_nondep_2560_;
v___y_2481_ = v_declName_2556_;
v___y_2482_ = v_a_2562_;
v___y_2483_ = v_a_2566_;
v___y_2484_ = v_body_2559_;
v___y_2485_ = v___x_2572_;
goto v___jp_2477_;
}
}
else
{
lean_dec(v_a_2564_);
lean_dec(v_a_2562_);
lean_dec_ref(v_body_2559_);
lean_dec_ref_known(v___y_2527_, 4);
lean_dec(v_declName_2556_);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2565_;
}
}
else
{
lean_dec(v_a_2562_);
lean_dec_ref(v_body_2559_);
lean_dec_ref_known(v___y_2527_, 4);
lean_dec(v_declName_2556_);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2563_;
}
}
else
{
lean_dec_ref(v_body_2559_);
lean_dec_ref_known(v___y_2527_, 4);
lean_dec(v_declName_2556_);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2561_;
}
}
case 5:
{
lean_object* v_dummy_2573_; lean_object* v_nargs_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_dummy_2573_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_2574_ = l_Lean_Expr_getAppNumArgs(v___y_2527_);
lean_inc(v_nargs_2574_);
v___x_2575_ = lean_mk_array(v_nargs_2574_, v_dummy_2573_);
v___x_2576_ = lean_unsigned_to_nat(1u);
v___x_2577_ = lean_nat_sub(v_nargs_2574_, v___x_2576_);
lean_dec(v_nargs_2574_);
v___x_2578_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2470_, v_post_2472_, v___y_2527_, v___x_2575_, v___x_2577_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2578_;
}
case 10:
{
lean_object* v_data_2579_; lean_object* v_expr_2580_; lean_object* v___x_2581_; 
v_data_2579_ = lean_ctor_get(v___y_2527_, 0);
v_expr_2580_ = lean_ctor_get(v___y_2527_, 1);
lean_inc_ref(v_expr_2580_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2581_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_expr_2580_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; size_t v___x_2583_; size_t v___x_2584_; uint8_t v___x_2585_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = lean_ptr_addr(v_expr_2580_);
v___x_2584_ = lean_ptr_addr(v_a_2582_);
v___x_2585_ = lean_usize_dec_eq(v___x_2583_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_inc(v_data_2579_);
lean_dec_ref_known(v___y_2527_, 2);
v___x_2586_ = l_Lean_Expr_mdata___override(v_data_2579_, v_a_2582_);
v___x_2587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2586_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; 
lean_dec(v_a_2582_);
v___x_2588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___y_2527_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2588_;
}
}
else
{
lean_dec_ref_known(v___y_2527_, 2);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2581_;
}
}
case 11:
{
lean_object* v_typeName_2589_; lean_object* v_idx_2590_; lean_object* v_struct_2591_; lean_object* v___x_2592_; 
v_typeName_2589_ = lean_ctor_get(v___y_2527_, 0);
v_idx_2590_ = lean_ctor_get(v___y_2527_, 1);
v_struct_2591_ = lean_ctor_get(v___y_2527_, 2);
lean_inc_ref(v_struct_2591_);
lean_inc_ref(v_post_2472_);
lean_inc_ref(v_pre_2470_);
v___x_2592_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2470_, v_post_2472_, v_struct_2591_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; size_t v___x_2594_; size_t v___x_2595_; uint8_t v___x_2596_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = lean_ptr_addr(v_struct_2591_);
v___x_2595_ = lean_ptr_addr(v_a_2593_);
v___x_2596_ = lean_usize_dec_eq(v___x_2594_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_inc(v_idx_2590_);
lean_inc(v_typeName_2589_);
lean_dec_ref_known(v___y_2527_, 3);
v___x_2597_ = l_Lean_Expr_proj___override(v_typeName_2589_, v_idx_2590_, v_a_2593_);
v___x_2598_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2597_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; 
lean_dec(v_a_2593_);
v___x_2599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___y_2527_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2599_;
}
}
else
{
lean_dec_ref_known(v___y_2527_, 3);
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_pre_2470_);
return v___x_2592_;
}
}
default: 
{
lean_object* v___x_2600_; 
v___x_2600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___y_2527_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2600_;
}
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_e_2471_);
lean_dec_ref(v_pre_2470_);
v_a_2612_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2521_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2521_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v_post_2472_);
lean_dec_ref(v_e_2471_);
lean_dec_ref(v_pre_2470_);
v_a_2620_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2520_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2520_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
v___jp_2477_:
{
if (v___y_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec_ref(v___y_2484_);
lean_dec_ref(v___y_2478_);
v___x_2486_ = l_Lean_Expr_letE___override(v___y_2481_, v___y_2482_, v___y_2479_, v___y_2483_, v___y_2480_);
v___x_2487_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2486_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2487_;
}
else
{
size_t v___x_2488_; size_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2488_ = lean_ptr_addr(v___y_2484_);
lean_dec_ref(v___y_2484_);
v___x_2489_ = lean_ptr_addr(v___y_2483_);
v___x_2490_ = lean_usize_dec_eq(v___x_2488_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_dec_ref(v___y_2478_);
v___x_2491_ = l_Lean_Expr_letE___override(v___y_2481_, v___y_2482_, v___y_2479_, v___y_2483_, v___y_2480_);
v___x_2492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2491_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; 
lean_dec_ref(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2479_);
v___x_2493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___y_2478_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2493_;
}
}
}
v___jp_2494_:
{
if (v___y_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec_ref(v___y_2495_);
v___x_2501_ = l_Lean_Expr_lam___override(v___y_2498_, v___y_2499_, v___y_2497_, v___y_2496_);
v___x_2502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2501_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2502_;
}
else
{
uint8_t v___x_2503_; 
v___x_2503_ = l_Lean_instBEqBinderInfo_beq(v___y_2496_, v___y_2496_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec_ref(v___y_2495_);
v___x_2504_ = l_Lean_Expr_lam___override(v___y_2498_, v___y_2499_, v___y_2497_, v___y_2496_);
v___x_2505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2504_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2505_;
}
else
{
lean_object* v___x_2506_; 
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
v___x_2506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___y_2495_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2506_;
}
}
}
v___jp_2507_:
{
if (v___y_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec_ref(v___y_2509_);
v___x_2514_ = l_Lean_Expr_forallE___override(v___y_2512_, v___y_2510_, v___y_2511_, v___y_2508_);
v___x_2515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2514_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2515_;
}
else
{
uint8_t v___x_2516_; 
v___x_2516_ = l_Lean_instBEqBinderInfo_beq(v___y_2508_, v___y_2508_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec_ref(v___y_2509_);
v___x_2517_ = l_Lean_Expr_forallE___override(v___y_2512_, v___y_2510_, v___y_2511_, v___y_2508_);
v___x_2518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___x_2517_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2518_;
}
else
{
lean_object* v___x_2519_; 
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v___y_2510_);
v___x_2519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2470_, v_post_2472_, v___y_2509_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2628_, lean_object* v_pre_2629_, lean_object* v_e_2630_, lean_object* v_post_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_2628_, v_pre_2629_, v_e_2630_, v_post_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object* v_pre_2637_, lean_object* v_post_2638_, lean_object* v_e_2639_, lean_object* v_a_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_inc(v_a_2640_);
v___x_2644_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2644_, 0, lean_box(0));
lean_closure_set(v___x_2644_, 1, lean_box(0));
lean_closure_set(v___x_2644_, 2, v_a_2640_);
v___x_2645_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___x_2644_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2677_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2677_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2677_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_2646_, v_e_2639_);
lean_dec(v_a_2646_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v___x_2651_; lean_object* v___f_2652_; lean_object* v___x_2653_; 
lean_del_object(v___x_2648_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_2639_);
v___f_2652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2652_, 0, v___x_2651_);
lean_closure_set(v___f_2652_, 1, v_pre_2637_);
lean_closure_set(v___f_2652_, 2, v_e_2639_);
lean_closure_set(v___f_2652_, 3, v_post_2638_);
v___x_2653_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2652_, v_a_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___f_2655_; lean_object* v___x_2656_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc_n(v_a_2654_, 2);
lean_dec_ref_known(v___x_2653_, 1);
lean_inc(v_a_2640_);
v___f_2655_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2655_, 0, v_a_2640_);
lean_closure_set(v___f_2655_, 1, v_e_2639_);
lean_closure_set(v___f_2655_, 2, v_a_2654_);
v___x_2656_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___f_2655_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2663_ == 0)
{
lean_object* v_unused_2664_; 
v_unused_2664_ = lean_ctor_get(v___x_2656_, 0);
lean_dec(v_unused_2664_);
v___x_2658_ = v___x_2656_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_dec(v___x_2656_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_a_2654_);
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2654_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_a_2654_);
v_a_2665_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2656_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2656_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_dec_ref(v_e_2639_);
return v___x_2653_;
}
}
else
{
lean_object* v_val_2673_; lean_object* v___x_2675_; 
lean_dec_ref(v_e_2639_);
lean_dec_ref(v_post_2638_);
lean_dec_ref(v_pre_2637_);
v_val_2673_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_val_2673_);
lean_dec_ref_known(v___x_2650_, 1);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_val_2673_);
v___x_2675_ = v___x_2648_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_val_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec_ref(v_e_2639_);
lean_dec_ref(v_post_2638_);
lean_dec_ref(v_pre_2637_);
v_a_2678_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2645_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2645_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object* v_pre_2686_, lean_object* v_post_2687_, lean_object* v_e_2688_, lean_object* v_a_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; 
lean_inc_ref(v_post_2687_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc_ref(v_e_2688_);
v___x_2693_ = lean_apply_4(v_post_2687_, v_e_2688_, v___y_2690_, v___y_2691_, lean_box(0));
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2712_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2712_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2712_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
switch(lean_obj_tag(v_a_2694_))
{
case 0:
{
lean_object* v_e_2698_; lean_object* v___x_2700_; 
lean_dec_ref(v_e_2688_);
lean_dec_ref(v_post_2687_);
lean_dec_ref(v_pre_2686_);
v_e_2698_ = lean_ctor_get(v_a_2694_, 0);
lean_inc_ref(v_e_2698_);
lean_dec_ref_known(v_a_2694_, 1);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_e_2698_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_e_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
case 1:
{
lean_object* v_e_2702_; lean_object* v___x_2703_; 
lean_del_object(v___x_2696_);
lean_dec_ref(v_e_2688_);
v_e_2702_ = lean_ctor_get(v_a_2694_, 0);
lean_inc_ref(v_e_2702_);
lean_dec_ref_known(v_a_2694_, 1);
v___x_2703_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2686_, v_post_2687_, v_e_2702_, v_a_2689_, v___y_2690_, v___y_2691_);
return v___x_2703_;
}
default: 
{
lean_object* v_e_x3f_2704_; 
lean_dec_ref(v_post_2687_);
lean_dec_ref(v_pre_2686_);
v_e_x3f_2704_ = lean_ctor_get(v_a_2694_, 0);
lean_inc(v_e_x3f_2704_);
lean_dec_ref_known(v_a_2694_, 1);
if (lean_obj_tag(v_e_x3f_2704_) == 0)
{
lean_object* v___x_2706_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_e_2688_);
v___x_2706_ = v___x_2696_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_e_2688_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
else
{
lean_object* v_val_2708_; lean_object* v___x_2710_; 
lean_dec_ref(v_e_2688_);
v_val_2708_ = lean_ctor_get(v_e_x3f_2704_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v_e_x3f_2704_, 1);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_val_2708_);
v___x_2710_ = v___x_2696_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_val_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_e_2688_);
lean_dec_ref(v_post_2687_);
lean_dec_ref(v_pre_2686_);
v_a_2713_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2693_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2693_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2721_, lean_object* v_post_2722_, lean_object* v_e_2723_, lean_object* v_a_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2721_, v_post_2722_, v_e_2723_, v_a_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v_a_2724_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2729_, lean_object* v_post_2730_, lean_object* v_sz_2731_, lean_object* v_i_2732_, lean_object* v_bs_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2731_);
lean_dec(v_sz_2731_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2729_, v_post_2730_, v_sz_boxed_2738_, v_i_boxed_2739_, v_bs_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_2741_, lean_object* v_post_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2741_, v_post_2742_, v_x_2743_, v_x_2744_, v_x_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(lean_object* v_pre_2751_, lean_object* v_post_2752_, lean_object* v_e_2753_, lean_object* v_a_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2751_, v_post_2752_, v_e_2753_, v_a_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v_a_2754_);
return v_res_2758_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0(void){
_start:
{
lean_object* v_cellCount_2759_; lean_object* v___x_2760_; 
v_cellCount_2759_ = lean_unsigned_to_nat(16u);
v___x_2760_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_2761_; lean_object* v___x_2762_; 
v_cellCount_2761_ = lean_unsigned_to_nat(16u);
v___x_2762_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
v___x_2764_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2764_);
lean_ctor_set(v___x_2766_, 2, v___x_2763_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_2768_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2768_, 0, lean_box(0));
lean_closure_set(v___x_2768_, 1, lean_box(0));
lean_closure_set(v___x_2768_, 2, v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object* v_input_2769_, lean_object* v_pre_2770_, lean_object* v_post_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_a_2777_; lean_object* v___x_2778_; 
v___x_2775_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3);
v___x_2776_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2775_, v___y_2772_, v___y_2773_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref(v___x_2776_);
v___x_2778_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2770_, v_post_2771_, v_input_2769_, v_a_2777_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2780_, 0, lean_box(0));
lean_closure_set(v___x_2780_, 1, lean_box(0));
lean_closure_set(v___x_2780_, 2, v_a_2777_);
v___x_2781_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2780_, v___y_2772_, v___y_2773_);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v___x_2781_, 0);
lean_dec(v_unused_2789_);
v___x_2783_ = v___x_2781_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v___x_2781_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v_a_2779_);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2779_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_dec(v_a_2777_);
return v___x_2778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object* v_input_2790_, lean_object* v_pre_2791_, lean_object* v_post_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2790_, v_pre_2791_, v_post_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* v_e_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v___f_2804_; lean_object* v___x_2805_; 
v___f_2804_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0));
v___x_2805_ = lean_find_expr(v___f_2804_, v_e_2800_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_e_2800_);
return v___x_2806_;
}
else
{
lean_object* v_pre_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; 
lean_dec_ref_known(v___x_2805_, 1);
v_pre_2807_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1));
v___f_2808_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2));
v___x_2809_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_e_2800_, v_pre_2807_, v___f_2808_, v_a_2801_, v_a_2802_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object* v_e_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2810_, v_a_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2815_, lean_object* v_m_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2816_, v_a_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2819_, lean_object* v_m_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_2819_, v_m_2820_, v_a_2821_);
lean_dec_ref(v_a_2821_);
lean_dec_ref(v_m_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_2823_, lean_object* v_ref_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2824_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2829_, lean_object* v_ref_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2829_, v_ref_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_2845_, lean_object* v_x_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2852_, lean_object* v_x_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_2852_, v_x_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2859_, lean_object* v_m_2860_, lean_object* v_query_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2860_, v_query_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_2863_, lean_object* v_m_2864_, lean_object* v_query_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(v_00_u03b2_2863_, v_m_2864_, v_query_2865_);
lean_dec_ref(v_query_2865_);
lean_dec_ref(v_m_2864_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7(lean_object* v_00_u03b2_2867_, lean_object* v_m_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___redArg(v_m_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b2_2870_, lean_object* v_m_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7(v_00_u03b2_2870_, v_m_2871_);
lean_dec_ref(v_m_2871_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_2873_, lean_object* v_m_2874_, lean_object* v_query_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_m_2874_, v_query_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2877_, lean_object* v_m_2878_, lean_object* v_query_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2877_, v_m_2878_, v_query_2879_);
lean_dec_ref(v_query_2879_);
lean_dec_ref(v_m_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_2881_, lean_object* v_m_2882_, lean_object* v_query_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_m_2882_, v_query_2883_, v_x_2884_, v_x_2885_, v_x_2886_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2889_, lean_object* v_m_2890_, lean_object* v_query_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_, lean_object* v_x_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_2889_, v_m_2890_, v_query_2891_, v_x_2892_, v_x_2893_, v_x_2894_, v_x_2895_);
lean_dec_ref(v_query_2891_);
lean_dec_ref(v_m_2890_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12(lean_object* v_00_u03b2_2897_, lean_object* v_init_2898_, lean_object* v_b_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___redArg(v_init_2898_, v_b_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12___boxed(lean_object* v_00_u03b2_2901_, lean_object* v_init_2902_, lean_object* v_b_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12(v_00_u03b2_2901_, v_init_2902_, v_b_2903_);
lean_dec_ref(v_b_2903_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_2905_, lean_object* v_b_2906_, lean_object* v_acc_2907_, lean_object* v_i_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_2906_, v_acc_2907_, v_i_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object* v_00_u03b2_2910_, lean_object* v_b_2911_, lean_object* v_acc_2912_, lean_object* v_i_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__7_spec__12_spec__13(v_00_u03b2_2910_, v_b_2911_, v_acc_2912_, v_i_2913_);
lean_dec_ref(v_b_2911_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_Meta_Sym_foldProjs(v_e_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Meta_Grind_foldProjs(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_2936_, lean_object* v_config_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_00___x40___internal___hyg_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = lean_grind_normalize(v_e_2936_, v_config_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
return v_res_2943_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_box(0);
v___x_2952_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2953_ = l_Lean_mkConst(v___x_2952_, v___x_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_2956_ = l_Lean_Expr_app___override(v___x_2955_, v_e_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_2957_){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2958_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = l_Lean_Expr_isAppOfArity(v_e_2957_, v___x_2958_, v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_2961_){
_start:
{
uint8_t v_res_2962_; lean_object* v_r_2963_; 
v_res_2962_ = l_Lean_Meta_Grind_isMatchCond(v_e_2961_);
lean_dec_ref(v_e_2961_);
v_r_2963_ = lean_box(v_res_2962_);
return v_r_2963_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = lean_box(0);
v___x_2970_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2971_ = l_Lean_mkConst(v___x_2970_, v___x_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_2972_){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_2974_ = l_Lean_Expr_app___override(v___x_2973_, v_e_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_2975_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2977_ = lean_unsigned_to_nat(1u);
v___x_2978_ = l_Lean_Expr_isAppOfArity(v_e_2975_, v___x_2976_, v___x_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_2979_){
_start:
{
uint8_t v_res_2980_; lean_object* v_r_2981_; 
v_res_2980_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_2979_);
lean_dec_ref(v_e_2979_);
v_r_2981_ = lean_box(v_res_2980_);
return v_r_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; 
lean_inc_ref(v_e_2984_);
v___x_2987_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3004_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_3004_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3004_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2997_ = l_Lean_Expr_cleanupAnnotations(v_a_2988_);
v___x_2998_ = l_Lean_Expr_isApp(v___x_2997_);
if (v___x_2998_ == 0)
{
lean_dec_ref(v___x_2997_);
lean_dec_ref(v_e_2984_);
goto v___jp_2992_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_2999_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2997_);
v___x_3000_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_3001_ = l_Lean_Expr_isConstOf(v___x_2999_, v___x_3000_);
lean_dec_ref(v___x_2999_);
if (v___x_3001_ == 0)
{
lean_dec_ref(v_e_2984_);
goto v___jp_2992_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_del_object(v___x_2990_);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_e_2984_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
v___jp_2992_:
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2993_ = ((lean_object*)(l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0));
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2993_);
v___x_2995_ = v___x_2990_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v_e_2984_);
v_a_3005_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2987_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2987_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_3013_, v_a_3014_);
lean_dec(v_a_3014_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_3017_, v_a_3022_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_3055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_3056_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_3057_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3054_, v___x_3055_, v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11____boxed(lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_3065_ = 0;
v___x_3066_ = l_Lean_Meta_Simp_Simprocs_add(v_s_3060_, v___x_3064_, v___x_3065_, v_a_3061_, v_a_3062_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
lean_inc_ref(v_e_3072_);
v___x_3082_ = l_Lean_Expr_cleanupAnnotations(v_e_3072_);
v___x_3083_ = l_Lean_Expr_isApp(v___x_3082_);
if (v___x_3083_ == 0)
{
lean_dec_ref(v___x_3082_);
goto v___jp_3078_;
}
else
{
lean_object* v_arg_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v_arg_3084_ = lean_ctor_get(v___x_3082_, 1);
lean_inc_ref(v_arg_3084_);
v___x_3085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3082_);
v___x_3086_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_3087_ = l_Lean_Expr_isConstOf(v___x_3085_, v___x_3086_);
lean_dec_ref(v___x_3085_);
if (v___x_3087_ == 0)
{
lean_dec_ref(v_arg_3084_);
goto v___jp_3078_;
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref(v_e_3072_);
v___x_3088_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_3084_);
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
v___jp_3078_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_e_3072_);
v___x_3080_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* v_e_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_e_3099_);
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_object* v_00_u03b1_3114_, lean_object* v_x_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_apply_1(v_x_3115_, lean_box(0));
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3123_, lean_object* v_x_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(v_00_u03b1_3123_, v_x_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___y_3139_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; uint8_t v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v_fileName_3169_; lean_object* v_fileMap_3170_; lean_object* v_options_3171_; lean_object* v_currRecDepth_3172_; lean_object* v_maxRecDepth_3173_; lean_object* v_ref_3174_; lean_object* v_currNamespace_3175_; lean_object* v_openDecls_3176_; lean_object* v_initHeartbeats_3177_; lean_object* v_maxHeartbeats_3178_; lean_object* v_quotContext_3179_; lean_object* v_currMacroScope_3180_; uint8_t v_diag_3181_; lean_object* v_cancelTk_x3f_3182_; uint8_t v_suppressElabErrors_3183_; lean_object* v_inheritedTraceOptions_3184_; 
v_fileName_3169_ = lean_ctor_get(v___y_3135_, 0);
v_fileMap_3170_ = lean_ctor_get(v___y_3135_, 1);
v_options_3171_ = lean_ctor_get(v___y_3135_, 2);
v_currRecDepth_3172_ = lean_ctor_get(v___y_3135_, 3);
v_maxRecDepth_3173_ = lean_ctor_get(v___y_3135_, 4);
v_ref_3174_ = lean_ctor_get(v___y_3135_, 5);
v_currNamespace_3175_ = lean_ctor_get(v___y_3135_, 6);
v_openDecls_3176_ = lean_ctor_get(v___y_3135_, 7);
v_initHeartbeats_3177_ = lean_ctor_get(v___y_3135_, 8);
v_maxHeartbeats_3178_ = lean_ctor_get(v___y_3135_, 9);
v_quotContext_3179_ = lean_ctor_get(v___y_3135_, 10);
v_currMacroScope_3180_ = lean_ctor_get(v___y_3135_, 11);
v_diag_3181_ = lean_ctor_get_uint8(v___y_3135_, sizeof(void*)*14);
v_cancelTk_x3f_3182_ = lean_ctor_get(v___y_3135_, 12);
v_suppressElabErrors_3183_ = lean_ctor_get_uint8(v___y_3135_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3184_ = lean_ctor_get(v___y_3135_, 13);
if (lean_obj_tag(v_cancelTk_x3f_3182_) == 1)
{
lean_object* v_val_3190_; uint8_t v___x_3191_; 
v_val_3190_ = lean_ctor_get(v_cancelTk_x3f_3182_, 0);
v___x_3191_ = l_IO_CancelToken_isSet(v_val_3190_);
if (v___x_3191_ == 0)
{
goto v___jp_3185_;
}
else
{
lean_object* v___x_3192_; lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v_x_3131_);
v___x_3192_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
goto v___jp_3185_;
}
v___jp_3138_:
{
if (lean_obj_tag(v___y_3139_) == 0)
{
return v___y_3139_;
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v___y_3139_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___y_3139_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___y_3139_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___y_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
v___jp_3148_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3165_ = lean_unsigned_to_nat(1u);
v___x_3166_ = lean_nat_add(v___y_3159_, v___x_3165_);
lean_inc_ref(v___y_3152_);
lean_inc(v___y_3162_);
lean_inc(v___y_3156_);
lean_inc(v___y_3164_);
lean_inc(v___y_3157_);
lean_inc(v___y_3149_);
lean_inc(v___y_3150_);
lean_inc(v___y_3151_);
lean_inc(v___y_3163_);
lean_inc_ref(v___y_3158_);
lean_inc_ref(v___y_3155_);
lean_inc_ref(v___y_3153_);
v___x_3167_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3167_, 0, v___y_3153_);
lean_ctor_set(v___x_3167_, 1, v___y_3155_);
lean_ctor_set(v___x_3167_, 2, v___y_3158_);
lean_ctor_set(v___x_3167_, 3, v___x_3166_);
lean_ctor_set(v___x_3167_, 4, v___y_3163_);
lean_ctor_set(v___x_3167_, 5, v___y_3161_);
lean_ctor_set(v___x_3167_, 6, v___y_3151_);
lean_ctor_set(v___x_3167_, 7, v___y_3150_);
lean_ctor_set(v___x_3167_, 8, v___y_3149_);
lean_ctor_set(v___x_3167_, 9, v___y_3157_);
lean_ctor_set(v___x_3167_, 10, v___y_3164_);
lean_ctor_set(v___x_3167_, 11, v___y_3156_);
lean_ctor_set(v___x_3167_, 12, v___y_3162_);
lean_ctor_set(v___x_3167_, 13, v___y_3152_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*14, v___y_3154_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*14 + 1, v___y_3160_);
lean_inc(v___y_3136_);
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
v___x_3168_ = lean_apply_6(v_x_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___x_3167_, v___y_3136_, lean_box(0));
v___y_3139_ = v___x_3168_;
goto v___jp_3138_;
}
v___jp_3185_:
{
lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = lean_unsigned_to_nat(0u);
v___x_3187_ = lean_nat_dec_eq(v_maxRecDepth_3173_, v___x_3186_);
if (v___x_3187_ == 0)
{
uint8_t v___x_3188_; 
v___x_3188_ = lean_nat_dec_eq(v_currRecDepth_3172_, v_maxRecDepth_3173_);
if (v___x_3188_ == 0)
{
lean_inc(v_ref_3174_);
v___y_3149_ = v_initHeartbeats_3177_;
v___y_3150_ = v_openDecls_3176_;
v___y_3151_ = v_currNamespace_3175_;
v___y_3152_ = v_inheritedTraceOptions_3184_;
v___y_3153_ = v_fileName_3169_;
v___y_3154_ = v_diag_3181_;
v___y_3155_ = v_fileMap_3170_;
v___y_3156_ = v_currMacroScope_3180_;
v___y_3157_ = v_maxHeartbeats_3178_;
v___y_3158_ = v_options_3171_;
v___y_3159_ = v_currRecDepth_3172_;
v___y_3160_ = v_suppressElabErrors_3183_;
v___y_3161_ = v_ref_3174_;
v___y_3162_ = v_cancelTk_x3f_3182_;
v___y_3163_ = v_maxRecDepth_3173_;
v___y_3164_ = v_quotContext_3179_;
goto v___jp_3148_;
}
else
{
lean_object* v___x_3189_; 
lean_dec_ref(v_x_3131_);
lean_inc(v_ref_3174_);
v___x_3189_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_3174_);
v___y_3139_ = v___x_3189_;
goto v___jp_3138_;
}
}
else
{
lean_inc(v_ref_3174_);
v___y_3149_ = v_initHeartbeats_3177_;
v___y_3150_ = v_openDecls_3176_;
v___y_3151_ = v_currNamespace_3175_;
v___y_3152_ = v_inheritedTraceOptions_3184_;
v___y_3153_ = v_fileName_3169_;
v___y_3154_ = v_diag_3181_;
v___y_3155_ = v_fileMap_3170_;
v___y_3156_ = v_currMacroScope_3180_;
v___y_3157_ = v_maxHeartbeats_3178_;
v___y_3158_ = v_options_3171_;
v___y_3159_ = v_currRecDepth_3172_;
v___y_3160_ = v_suppressElabErrors_3183_;
v___y_3161_ = v_ref_3174_;
v___y_3162_ = v_cancelTk_x3f_3182_;
v___y_3163_ = v_maxRecDepth_3173_;
v___y_3164_ = v_quotContext_3179_;
goto v___jp_3148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_apply_1(v_x_3210_, lean_box(0));
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3218_, lean_object* v_x_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(v_00_u03b1_3218_, v_x_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_3226_, lean_object* v_post_3227_, size_t v_sz_3228_, size_t v_i_3229_, lean_object* v_bs_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
uint8_t v___x_3237_; 
v___x_3237_ = lean_usize_dec_lt(v_i_3229_, v_sz_3228_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; 
lean_dec_ref(v_post_3227_);
lean_dec_ref(v_pre_3226_);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_bs_3230_);
return v___x_3238_;
}
else
{
lean_object* v_v_3239_; lean_object* v___x_3240_; 
v_v_3239_ = lean_array_uget_borrowed(v_bs_3230_, v_i_3229_);
lean_inc(v_v_3239_);
lean_inc_ref(v_post_3227_);
lean_inc_ref(v_pre_3226_);
v___x_3240_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3226_, v_post_3227_, v_v_3239_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3242_; lean_object* v_bs_x27_3243_; size_t v___x_3244_; size_t v___x_3245_; lean_object* v___x_3246_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3240_, 1);
v___x_3242_ = lean_unsigned_to_nat(0u);
v_bs_x27_3243_ = lean_array_uset(v_bs_3230_, v_i_3229_, v___x_3242_);
v___x_3244_ = ((size_t)1ULL);
v___x_3245_ = lean_usize_add(v_i_3229_, v___x_3244_);
v___x_3246_ = lean_array_uset(v_bs_x27_3243_, v_i_3229_, v_a_3241_);
v_i_3229_ = v___x_3245_;
v_bs_3230_ = v___x_3246_;
goto _start;
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v_bs_3230_);
lean_dec_ref(v_post_3227_);
lean_dec_ref(v_pre_3226_);
v_a_3248_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3240_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3240_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_3256_, lean_object* v_post_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 5)
{
lean_object* v_fn_3267_; lean_object* v_arg_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_fn_3267_ = lean_ctor_get(v_x_3258_, 0);
lean_inc_ref(v_fn_3267_);
v_arg_3268_ = lean_ctor_get(v_x_3258_, 1);
lean_inc_ref(v_arg_3268_);
lean_dec_ref_known(v_x_3258_, 2);
v___x_3269_ = lean_array_set(v_x_3259_, v_x_3260_, v_arg_3268_);
v___x_3270_ = lean_unsigned_to_nat(1u);
v___x_3271_ = lean_nat_sub(v_x_3260_, v___x_3270_);
lean_dec(v_x_3260_);
v_x_3258_ = v_fn_3267_;
v_x_3259_ = v___x_3269_;
v_x_3260_ = v___x_3271_;
goto _start;
}
else
{
lean_object* v___x_3273_; 
lean_dec(v_x_3260_);
lean_inc_ref(v_post_3257_);
lean_inc_ref(v_pre_3256_);
v___x_3273_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3256_, v_post_3257_, v_x_3258_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; size_t v_sz_3275_; size_t v___x_3276_; lean_object* v___x_3277_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v_sz_3275_ = lean_array_size(v_x_3259_);
v___x_3276_ = ((size_t)0ULL);
lean_inc_ref(v_post_3257_);
lean_inc_ref(v_pre_3256_);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3256_, v_post_3257_, v_sz_3275_, v___x_3276_, v_x_3259_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = l_Lean_mkAppN(v_a_3274_, v_a_3278_);
lean_dec(v_a_3278_);
v___x_3280_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3256_, v_post_3257_, v___x_3279_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v___x_3280_;
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v_a_3274_);
lean_dec_ref(v_post_3257_);
lean_dec_ref(v_pre_3256_);
v_a_3281_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3277_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3277_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_dec_ref(v_x_3259_);
lean_dec_ref(v_post_3257_);
lean_dec_ref(v_pre_3256_);
return v___x_3273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v___x_3289_, lean_object* v_pre_3290_, lean_object* v_e_3291_, lean_object* v_post_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; uint8_t v___y_3307_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; uint8_t v___y_3321_; uint8_t v___y_3322_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; uint8_t v___y_3334_; uint8_t v___y_3335_; lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_Core_checkSystem(v___x_3289_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v___x_3343_; 
lean_dec_ref_known(v___x_3342_, 1);
lean_inc_ref(v_pre_3290_);
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3294_);
lean_inc_ref(v_e_3291_);
v___x_3343_ = lean_apply_6(v_pre_3290_, v_e_3291_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, lean_box(0));
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3433_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3433_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3433_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___y_3349_; 
switch(lean_obj_tag(v_a_3344_))
{
case 0:
{
lean_object* v_e_3423_; lean_object* v___x_3425_; 
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_e_3291_);
lean_dec_ref(v_pre_3290_);
v_e_3423_ = lean_ctor_get(v_a_3344_, 0);
lean_inc_ref(v_e_3423_);
lean_dec_ref_known(v_a_3344_, 1);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v_e_3423_);
v___x_3425_ = v___x_3346_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_e_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
case 1:
{
lean_object* v_e_3427_; lean_object* v___x_3428_; 
lean_del_object(v___x_3346_);
lean_dec_ref(v_e_3291_);
v_e_3427_ = lean_ctor_get(v_a_3344_, 0);
lean_inc_ref(v_e_3427_);
lean_dec_ref_known(v_a_3344_, 1);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_e_3427_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v___x_3430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v_a_3429_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3430_;
}
else
{
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3428_;
}
}
default: 
{
lean_object* v_e_x3f_3431_; 
lean_del_object(v___x_3346_);
v_e_x3f_3431_ = lean_ctor_get(v_a_3344_, 0);
lean_inc(v_e_x3f_3431_);
lean_dec_ref_known(v_a_3344_, 1);
if (lean_obj_tag(v_e_x3f_3431_) == 0)
{
v___y_3349_ = v_e_3291_;
goto v___jp_3348_;
}
else
{
lean_object* v_val_3432_; 
lean_dec_ref(v_e_3291_);
v_val_3432_ = lean_ctor_get(v_e_x3f_3431_, 0);
lean_inc(v_val_3432_);
lean_dec_ref_known(v_e_x3f_3431_, 1);
v___y_3349_ = v_val_3432_;
goto v___jp_3348_;
}
}
}
v___jp_3348_:
{
switch(lean_obj_tag(v___y_3349_))
{
case 7:
{
lean_object* v_binderName_3350_; lean_object* v_binderType_3351_; lean_object* v_body_3352_; uint8_t v_binderInfo_3353_; lean_object* v___x_3354_; 
v_binderName_3350_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_binderName_3350_);
v_binderType_3351_ = lean_ctor_get(v___y_3349_, 1);
v_body_3352_ = lean_ctor_get(v___y_3349_, 2);
v_binderInfo_3353_ = lean_ctor_get_uint8(v___y_3349_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3351_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3354_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_binderType_3351_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
lean_inc_ref(v_body_3352_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3356_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_body_3352_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; size_t v___x_3358_; size_t v___x_3359_; uint8_t v___x_3360_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = lean_ptr_addr(v_binderType_3351_);
v___x_3359_ = lean_ptr_addr(v_a_3355_);
v___x_3360_ = lean_usize_dec_eq(v___x_3358_, v___x_3359_);
if (v___x_3360_ == 0)
{
v___y_3330_ = v_a_3355_;
v___y_3331_ = v_binderName_3350_;
v___y_3332_ = v_a_3357_;
v___y_3333_ = v___y_3349_;
v___y_3334_ = v_binderInfo_3353_;
v___y_3335_ = v___x_3360_;
goto v___jp_3329_;
}
else
{
size_t v___x_3361_; size_t v___x_3362_; uint8_t v___x_3363_; 
v___x_3361_ = lean_ptr_addr(v_body_3352_);
v___x_3362_ = lean_ptr_addr(v_a_3357_);
v___x_3363_ = lean_usize_dec_eq(v___x_3361_, v___x_3362_);
v___y_3330_ = v_a_3355_;
v___y_3331_ = v_binderName_3350_;
v___y_3332_ = v_a_3357_;
v___y_3333_ = v___y_3349_;
v___y_3334_ = v_binderInfo_3353_;
v___y_3335_ = v___x_3363_;
goto v___jp_3329_;
}
}
else
{
lean_dec(v_a_3355_);
lean_dec_ref_known(v___y_3349_, 3);
lean_dec(v_binderName_3350_);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3356_;
}
}
else
{
lean_dec_ref_known(v___y_3349_, 3);
lean_dec(v_binderName_3350_);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3354_;
}
}
case 6:
{
lean_object* v_binderName_3364_; lean_object* v_binderType_3365_; lean_object* v_body_3366_; uint8_t v_binderInfo_3367_; lean_object* v___x_3368_; 
v_binderName_3364_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_binderName_3364_);
v_binderType_3365_ = lean_ctor_get(v___y_3349_, 1);
v_body_3366_ = lean_ctor_get(v___y_3349_, 2);
v_binderInfo_3367_ = lean_ctor_get_uint8(v___y_3349_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3365_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3368_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_binderType_3365_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3370_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3368_, 1);
lean_inc_ref(v_body_3366_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3370_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_body_3366_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; size_t v___x_3372_; size_t v___x_3373_; uint8_t v___x_3374_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = lean_ptr_addr(v_binderType_3365_);
v___x_3373_ = lean_ptr_addr(v_a_3369_);
v___x_3374_ = lean_usize_dec_eq(v___x_3372_, v___x_3373_);
if (v___x_3374_ == 0)
{
v___y_3317_ = v_a_3371_;
v___y_3318_ = v___y_3349_;
v___y_3319_ = v_binderName_3364_;
v___y_3320_ = v_a_3369_;
v___y_3321_ = v_binderInfo_3367_;
v___y_3322_ = v___x_3374_;
goto v___jp_3316_;
}
else
{
size_t v___x_3375_; size_t v___x_3376_; uint8_t v___x_3377_; 
v___x_3375_ = lean_ptr_addr(v_body_3366_);
v___x_3376_ = lean_ptr_addr(v_a_3371_);
v___x_3377_ = lean_usize_dec_eq(v___x_3375_, v___x_3376_);
v___y_3317_ = v_a_3371_;
v___y_3318_ = v___y_3349_;
v___y_3319_ = v_binderName_3364_;
v___y_3320_ = v_a_3369_;
v___y_3321_ = v_binderInfo_3367_;
v___y_3322_ = v___x_3377_;
goto v___jp_3316_;
}
}
else
{
lean_dec(v_a_3369_);
lean_dec(v_binderName_3364_);
lean_dec_ref_known(v___y_3349_, 3);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3370_;
}
}
else
{
lean_dec_ref_known(v___y_3349_, 3);
lean_dec(v_binderName_3364_);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3368_;
}
}
case 8:
{
lean_object* v_declName_3378_; lean_object* v_type_3379_; lean_object* v_value_3380_; lean_object* v_body_3381_; uint8_t v_nondep_3382_; lean_object* v___x_3383_; 
v_declName_3378_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_declName_3378_);
v_type_3379_ = lean_ctor_get(v___y_3349_, 1);
v_value_3380_ = lean_ctor_get(v___y_3349_, 2);
v_body_3381_ = lean_ctor_get(v___y_3349_, 3);
lean_inc_ref(v_body_3381_);
v_nondep_3382_ = lean_ctor_get_uint8(v___y_3349_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3379_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3383_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_type_3379_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3385_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
lean_inc_ref(v_value_3380_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3385_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_value_3380_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
lean_inc_ref(v_body_3381_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3387_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_body_3381_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; size_t v___x_3389_; size_t v___x_3390_; uint8_t v___x_3391_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = lean_ptr_addr(v_type_3379_);
v___x_3390_ = lean_ptr_addr(v_a_3384_);
v___x_3391_ = lean_usize_dec_eq(v___x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
v___y_3300_ = v_a_3384_;
v___y_3301_ = v_a_3386_;
v___y_3302_ = v___y_3349_;
v___y_3303_ = v_a_3388_;
v___y_3304_ = v_nondep_3382_;
v___y_3305_ = v_body_3381_;
v___y_3306_ = v_declName_3378_;
v___y_3307_ = v___x_3391_;
goto v___jp_3299_;
}
else
{
size_t v___x_3392_; size_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = lean_ptr_addr(v_value_3380_);
v___x_3393_ = lean_ptr_addr(v_a_3386_);
v___x_3394_ = lean_usize_dec_eq(v___x_3392_, v___x_3393_);
v___y_3300_ = v_a_3384_;
v___y_3301_ = v_a_3386_;
v___y_3302_ = v___y_3349_;
v___y_3303_ = v_a_3388_;
v___y_3304_ = v_nondep_3382_;
v___y_3305_ = v_body_3381_;
v___y_3306_ = v_declName_3378_;
v___y_3307_ = v___x_3394_;
goto v___jp_3299_;
}
}
else
{
lean_dec(v_a_3386_);
lean_dec(v_a_3384_);
lean_dec_ref(v_body_3381_);
lean_dec(v_declName_3378_);
lean_dec_ref_known(v___y_3349_, 4);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3387_;
}
}
else
{
lean_dec(v_a_3384_);
lean_dec_ref(v_body_3381_);
lean_dec(v_declName_3378_);
lean_dec_ref_known(v___y_3349_, 4);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3385_;
}
}
else
{
lean_dec_ref(v_body_3381_);
lean_dec_ref_known(v___y_3349_, 4);
lean_dec(v_declName_3378_);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3383_;
}
}
case 5:
{
lean_object* v_dummy_3395_; lean_object* v_nargs_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v_dummy_3395_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3396_ = l_Lean_Expr_getAppNumArgs(v___y_3349_);
lean_inc(v_nargs_3396_);
v___x_3397_ = lean_mk_array(v_nargs_3396_, v_dummy_3395_);
v___x_3398_ = lean_unsigned_to_nat(1u);
v___x_3399_ = lean_nat_sub(v_nargs_3396_, v___x_3398_);
lean_dec(v_nargs_3396_);
v___x_3400_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3290_, v_post_3292_, v___y_3349_, v___x_3397_, v___x_3399_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3400_;
}
case 10:
{
lean_object* v_data_3401_; lean_object* v_expr_3402_; lean_object* v___x_3403_; 
v_data_3401_ = lean_ctor_get(v___y_3349_, 0);
v_expr_3402_ = lean_ctor_get(v___y_3349_, 1);
lean_inc_ref(v_expr_3402_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_expr_3402_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; size_t v___x_3405_; size_t v___x_3406_; uint8_t v___x_3407_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3403_, 1);
v___x_3405_ = lean_ptr_addr(v_expr_3402_);
v___x_3406_ = lean_ptr_addr(v_a_3404_);
v___x_3407_ = lean_usize_dec_eq(v___x_3405_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_inc(v_data_3401_);
lean_dec_ref_known(v___y_3349_, 2);
v___x_3408_ = l_Lean_Expr_mdata___override(v_data_3401_, v_a_3404_);
v___x_3409_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3408_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3409_;
}
else
{
lean_object* v___x_3410_; 
lean_dec(v_a_3404_);
v___x_3410_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___y_3349_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3410_;
}
}
else
{
lean_dec_ref_known(v___y_3349_, 2);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3403_;
}
}
case 11:
{
lean_object* v_typeName_3411_; lean_object* v_idx_3412_; lean_object* v_struct_3413_; lean_object* v___x_3414_; 
v_typeName_3411_ = lean_ctor_get(v___y_3349_, 0);
v_idx_3412_ = lean_ctor_get(v___y_3349_, 1);
v_struct_3413_ = lean_ctor_get(v___y_3349_, 2);
lean_inc_ref(v_struct_3413_);
lean_inc_ref(v_post_3292_);
lean_inc_ref(v_pre_3290_);
v___x_3414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3290_, v_post_3292_, v_struct_3413_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; size_t v___x_3416_; size_t v___x_3417_; uint8_t v___x_3418_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v___x_3416_ = lean_ptr_addr(v_struct_3413_);
v___x_3417_ = lean_ptr_addr(v_a_3415_);
v___x_3418_ = lean_usize_dec_eq(v___x_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
lean_inc(v_idx_3412_);
lean_inc(v_typeName_3411_);
lean_dec_ref_known(v___y_3349_, 3);
v___x_3419_ = l_Lean_Expr_proj___override(v_typeName_3411_, v_idx_3412_, v_a_3415_);
v___x_3420_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3419_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3420_;
}
else
{
lean_object* v___x_3421_; 
lean_dec(v_a_3415_);
v___x_3421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___y_3349_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3421_;
}
}
else
{
lean_dec_ref_known(v___y_3349_, 3);
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_pre_3290_);
return v___x_3414_;
}
}
default: 
{
lean_object* v___x_3422_; 
v___x_3422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___y_3349_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3422_;
}
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_e_3291_);
lean_dec_ref(v_pre_3290_);
v_a_3434_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3343_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3343_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec_ref(v_post_3292_);
lean_dec_ref(v_e_3291_);
lean_dec_ref(v_pre_3290_);
v_a_3442_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3342_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3342_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
v___jp_3299_:
{
if (v___y_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec_ref(v___y_3305_);
lean_dec_ref(v___y_3302_);
v___x_3308_ = l_Lean_Expr_letE___override(v___y_3306_, v___y_3300_, v___y_3301_, v___y_3303_, v___y_3304_);
v___x_3309_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3308_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3309_;
}
else
{
size_t v___x_3310_; size_t v___x_3311_; uint8_t v___x_3312_; 
v___x_3310_ = lean_ptr_addr(v___y_3305_);
lean_dec_ref(v___y_3305_);
v___x_3311_ = lean_ptr_addr(v___y_3303_);
v___x_3312_ = lean_usize_dec_eq(v___x_3310_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
lean_dec_ref(v___y_3302_);
v___x_3313_ = l_Lean_Expr_letE___override(v___y_3306_, v___y_3300_, v___y_3301_, v___y_3303_, v___y_3304_);
v___x_3314_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3313_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; 
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3303_);
lean_dec_ref(v___y_3301_);
lean_dec_ref(v___y_3300_);
v___x_3315_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___y_3302_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3315_;
}
}
}
v___jp_3316_:
{
if (v___y_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec_ref(v___y_3318_);
v___x_3323_ = l_Lean_Expr_lam___override(v___y_3319_, v___y_3320_, v___y_3317_, v___y_3321_);
v___x_3324_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3323_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3324_;
}
else
{
uint8_t v___x_3325_; 
v___x_3325_ = l_Lean_instBEqBinderInfo_beq(v___y_3321_, v___y_3321_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_dec_ref(v___y_3318_);
v___x_3326_ = l_Lean_Expr_lam___override(v___y_3319_, v___y_3320_, v___y_3317_, v___y_3321_);
v___x_3327_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3326_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3327_;
}
else
{
lean_object* v___x_3328_; 
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3317_);
v___x_3328_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___y_3318_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3328_;
}
}
}
v___jp_3329_:
{
if (v___y_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
lean_dec_ref(v___y_3333_);
v___x_3336_ = l_Lean_Expr_forallE___override(v___y_3331_, v___y_3330_, v___y_3332_, v___y_3334_);
v___x_3337_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3336_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3337_;
}
else
{
uint8_t v___x_3338_; 
v___x_3338_ = l_Lean_instBEqBinderInfo_beq(v___y_3334_, v___y_3334_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_dec_ref(v___y_3333_);
v___x_3339_ = l_Lean_Expr_forallE___override(v___y_3331_, v___y_3330_, v___y_3332_, v___y_3334_);
v___x_3340_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___x_3339_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3340_;
}
else
{
lean_object* v___x_3341_; 
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
v___x_3341_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3290_, v_post_3292_, v___y_3333_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v___x_3450_, lean_object* v_pre_3451_, lean_object* v_e_3452_, lean_object* v_post_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_3450_, v_pre_3451_, v_e_3452_, v_post_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_3461_, lean_object* v_post_3462_, lean_object* v_e_3463_, lean_object* v_a_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_inc(v_a_3464_);
v___x_3470_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3470_, 0, lean_box(0));
lean_closure_set(v___x_3470_, 1, lean_box(0));
lean_closure_set(v___x_3470_, 2, v_a_3464_);
v___x_3471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___x_3470_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3503_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3503_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3503_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3472_, v_e_3463_);
lean_dec(v_a_3472_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v___x_3477_; lean_object* v___f_3478_; lean_object* v___x_3479_; 
lean_del_object(v___x_3474_);
v___x_3477_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_3463_);
v___f_3478_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3478_, 0, v___x_3477_);
lean_closure_set(v___f_3478_, 1, v_pre_3461_);
lean_closure_set(v___f_3478_, 2, v_e_3463_);
lean_closure_set(v___f_3478_, 3, v_post_3462_);
v___x_3479_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_3478_, v_a_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___f_3481_; lean_object* v___x_3482_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc_n(v_a_3480_, 2);
lean_dec_ref_known(v___x_3479_, 1);
lean_inc(v_a_3464_);
v___f_3481_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3481_, 0, v_a_3464_);
lean_closure_set(v___f_3481_, 1, v_e_3463_);
lean_closure_set(v___f_3481_, 2, v_a_3480_);
v___x_3482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___f_3481_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v___x_3482_, 0);
lean_dec(v_unused_3490_);
v___x_3484_ = v___x_3482_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_dec(v___x_3482_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v_a_3480_);
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3480_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_a_3480_);
v_a_3491_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3482_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3482_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
lean_dec_ref(v_e_3463_);
return v___x_3479_;
}
}
else
{
lean_object* v_val_3499_; lean_object* v___x_3501_; 
lean_dec_ref(v_e_3463_);
lean_dec_ref(v_post_3462_);
lean_dec_ref(v_pre_3461_);
v_val_3499_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v___x_3476_, 1);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_val_3499_);
v___x_3501_ = v___x_3474_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_val_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_e_3463_);
lean_dec_ref(v_post_3462_);
lean_dec_ref(v_pre_3461_);
v_a_3504_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3471_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3471_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_3512_, lean_object* v_post_3513_, lean_object* v_e_3514_, lean_object* v_a_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___x_3521_; 
lean_inc_ref(v_post_3513_);
lean_inc(v___y_3519_);
lean_inc_ref(v___y_3518_);
lean_inc(v___y_3517_);
lean_inc_ref(v___y_3516_);
lean_inc_ref(v_e_3514_);
v___x_3521_ = lean_apply_6(v_post_3513_, v_e_3514_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, lean_box(0));
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3540_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3524_ = v___x_3521_;
v_isShared_3525_ = v_isSharedCheck_3540_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3540_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
switch(lean_obj_tag(v_a_3522_))
{
case 0:
{
lean_object* v_e_3526_; lean_object* v___x_3528_; 
lean_dec_ref(v_e_3514_);
lean_dec_ref(v_post_3513_);
lean_dec_ref(v_pre_3512_);
v_e_3526_ = lean_ctor_get(v_a_3522_, 0);
lean_inc_ref(v_e_3526_);
lean_dec_ref_known(v_a_3522_, 1);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v_e_3526_);
v___x_3528_ = v___x_3524_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_e_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
case 1:
{
lean_object* v_e_3530_; lean_object* v___x_3531_; 
lean_del_object(v___x_3524_);
lean_dec_ref(v_e_3514_);
v_e_3530_ = lean_ctor_get(v_a_3522_, 0);
lean_inc_ref(v_e_3530_);
lean_dec_ref_known(v_a_3522_, 1);
v___x_3531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3512_, v_post_3513_, v_e_3530_, v_a_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
return v___x_3531_;
}
default: 
{
lean_object* v_e_x3f_3532_; 
lean_dec_ref(v_post_3513_);
lean_dec_ref(v_pre_3512_);
v_e_x3f_3532_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_e_x3f_3532_);
lean_dec_ref_known(v_a_3522_, 1);
if (lean_obj_tag(v_e_x3f_3532_) == 0)
{
lean_object* v___x_3534_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v_e_3514_);
v___x_3534_ = v___x_3524_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_e_3514_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
else
{
lean_object* v_val_3536_; lean_object* v___x_3538_; 
lean_dec_ref(v_e_3514_);
v_val_3536_ = lean_ctor_get(v_e_x3f_3532_, 0);
lean_inc(v_val_3536_);
lean_dec_ref_known(v_e_x3f_3532_, 1);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v_val_3536_);
v___x_3538_ = v___x_3524_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_val_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec_ref(v_e_3514_);
lean_dec_ref(v_post_3513_);
lean_dec_ref(v_pre_3512_);
v_a_3541_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3521_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3521_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_3549_, lean_object* v_post_3550_, lean_object* v_e_3551_, lean_object* v_a_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3549_, v_post_3550_, v_e_3551_, v_a_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v_a_3552_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_3559_, lean_object* v_post_3560_, lean_object* v_sz_3561_, lean_object* v_i_3562_, lean_object* v_bs_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
size_t v_sz_boxed_3570_; size_t v_i_boxed_3571_; lean_object* v_res_3572_; 
v_sz_boxed_3570_ = lean_unbox_usize(v_sz_3561_);
lean_dec(v_sz_3561_);
v_i_boxed_3571_ = lean_unbox_usize(v_i_3562_);
lean_dec(v_i_3562_);
v_res_3572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3559_, v_post_3560_, v_sz_boxed_3570_, v_i_boxed_3571_, v_bs_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_3573_, lean_object* v_post_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_, lean_object* v_x_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3573_, v_post_3574_, v_x_3575_, v_x_3576_, v_x_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_3585_, lean_object* v_post_3586_, lean_object* v_e_3587_, lean_object* v_a_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3585_, v_post_3586_, v_e_3587_, v_a_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v_a_3588_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_3595_, lean_object* v_pre_3596_, lean_object* v_post_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v_a_3605_; lean_object* v___x_3606_; 
v___x_3603_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__3);
v___x_3604_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3603_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___x_3604_);
v___x_3606_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3596_, v_post_3597_, v_input_3595_, v_a_3605_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v___x_3608_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3608_, 0, lean_box(0));
lean_closure_set(v___x_3608_, 1, lean_box(0));
lean_closure_set(v___x_3608_, 2, v_a_3605_);
v___x_3609_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3608_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v___x_3609_, 0);
lean_dec(v_unused_3617_);
v___x_3611_ = v___x_3609_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_dec(v___x_3609_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 0, v_a_3607_);
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3607_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
else
{
lean_dec(v_a_3605_);
return v___x_3606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_3618_, lean_object* v_pre_3619_, lean_object* v_post_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_3618_, v_pre_3619_, v_post_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_3637_ = lean_find_expr(v___x_3636_, v_e_3630_);
if (lean_obj_tag(v___x_3637_) == 0)
{
uint8_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = 1;
v___x_3639_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3639_, 0, v_e_3630_);
lean_ctor_set(v___x_3639_, 1, v___x_3637_);
lean_ctor_set_uint8(v___x_3639_, sizeof(void*)*2, v___x_3638_);
v___x_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
return v___x_3640_;
}
else
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3689_; 
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3637_, 0);
lean_dec(v_unused_3690_);
v___x_3642_ = v___x_3637_;
v_isShared_3643_ = v_isSharedCheck_3689_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v___x_3637_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3689_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v_pre_3644_; lean_object* v___f_3645_; lean_object* v___x_3646_; 
v_pre_3644_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_3645_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
lean_inc_ref(v_e_3630_);
v___x_3646_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_3630_, v_pre_3644_, v___f_3645_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc_n(v_a_3647_, 2);
lean_dec_ref_known(v___x_3646_, 1);
v___x_3648_ = l_Lean_Meta_mkEqRefl(v_a_3647_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
lean_inc(v_a_3647_);
v___x_3650_ = l_Lean_Meta_mkEq(v_e_3630_, v_a_3647_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3664_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3664_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3664_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
uint8_t v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3655_ = 1;
v___x_3656_ = l_Lean_Meta_mkExpectedPropHint(v_a_3649_, v_a_3651_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3656_);
v___x_3658_ = v___x_3642_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3659_, 0, v_a_3647_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*2, v___x_3655_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3659_);
v___x_3661_ = v___x_3653_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec(v_a_3649_);
lean_dec(v_a_3647_);
lean_del_object(v___x_3642_);
v_a_3665_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3650_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3650_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec(v_a_3647_);
lean_del_object(v___x_3642_);
lean_dec_ref(v_e_3630_);
v_a_3673_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3648_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3648_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3642_);
lean_dec_ref(v_e_3630_);
v_a_3681_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3646_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3646_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
lean_dec(v_a_3695_);
lean_dec_ref(v_a_3694_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3698_, lean_object* v_x_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3707_, lean_object* v_x_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_3707_, v_x_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
return v_res_3715_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_3719_){
_start:
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_3721_ = l_Lean_Expr_isAppOf(v_e_3719_, v___x_3720_);
if (v___x_3721_ == 0)
{
return v___x_3721_;
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3722_ = lean_unsigned_to_nat(5u);
v___x_3723_ = l_Lean_Expr_getAppNumArgs(v_e_3719_);
v___x_3724_ = lean_nat_dec_le(v___x_3722_, v___x_3723_);
lean_dec(v___x_3723_);
return v___x_3724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_3725_){
_start:
{
uint8_t v_res_3726_; lean_object* v_r_3727_; 
v_res_3726_ = l_Lean_Meta_Grind_isIte(v_e_3725_);
lean_dec_ref(v_e_3725_);
v_r_3727_ = lean_box(v_res_3726_);
return v_r_3727_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_3731_){
_start:
{
lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3732_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_3733_ = l_Lean_Expr_isAppOf(v_e_3731_, v___x_3732_);
if (v___x_3733_ == 0)
{
return v___x_3733_;
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3734_ = lean_unsigned_to_nat(5u);
v___x_3735_ = l_Lean_Expr_getAppNumArgs(v_e_3731_);
v___x_3736_ = lean_nat_dec_le(v___x_3734_, v___x_3735_);
lean_dec(v___x_3735_);
return v___x_3736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_3737_){
_start:
{
uint8_t v_res_3738_; lean_object* v_r_3739_; 
v_res_3738_ = l_Lean_Meta_Grind_isDIte(v_e_3737_);
lean_dec_ref(v_e_3737_);
v_r_3739_ = lean_box(v_res_3738_);
return v_r_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_3740_){
_start:
{
uint8_t v___x_3741_; 
v___x_3741_ = l_Lean_Expr_isApp(v_e_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_box(0);
return v___x_3742_;
}
else
{
lean_object* v_f_3743_; uint8_t v___x_3744_; 
v_f_3743_ = l_Lean_Expr_appFn_x21(v_e_3740_);
v___x_3744_ = l_Lean_Expr_isApp(v_f_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; 
lean_dec_ref(v_f_3743_);
v___x_3745_ = lean_box(0);
return v___x_3745_;
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = l_Lean_Expr_appFn_x21(v_f_3743_);
lean_dec_ref(v_f_3743_);
v___x_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
return v___x_3747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Meta_Grind_getBinOp(v_e_3748_);
lean_dec_ref(v_e_3748_);
return v_res_3749_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Init_Grind_Config(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Util(builtin);
}
#ifdef __cplusplus
}
#endif
