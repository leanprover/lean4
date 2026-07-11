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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
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
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "reducePreMatchCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(150, 224, 247, 141, 87, 215, 99, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(lean_object*);
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__4(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__3));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__5(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Lean_MVarId_ensureNoMVar___closed__4, &l_Lean_MVarId_ensureNoMVar___closed__4_once, _init_l_Lean_MVarId_ensureNoMVar___closed__4);
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar(lean_object* v_mvarId_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_mvarId_55_);
v___x_61_ = l_Lean_MVarId_getType(v_mvarId_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_76_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_61_, 1);
v___x_63_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_62_, v_a_57_);
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_76_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
uint8_t v___x_68_; 
v___x_68_ = l_Lean_Expr_hasExprMVar(v_a_64_);
lean_dec(v_a_64_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_71_; 
lean_dec(v_mvarId_55_);
v___x_69_ = lean_box(0);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_69_);
v___x_71_ = v___x_66_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_del_object(v___x_66_);
v___x_73_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_74_ = lean_obj_once(&l_Lean_MVarId_ensureNoMVar___closed__5, &l_Lean_MVarId_ensureNoMVar___closed__5_once, _init_l_Lean_MVarId_ensureNoMVar___closed__5);
v___x_75_ = l_Lean_Meta_throwTacticEx___redArg(v___x_73_, v_mvarId_55_, v___x_74_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
return v___x_75_;
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v_mvarId_55_);
v_a_77_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_61_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_61_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar___boxed(lean_object* v_mvarId_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_MVarId_ensureNoMVar(v_mvarId_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
return v_res_91_;
}
}
static lean_object* _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_instMonadEIO(lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_toApplicative_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_166_; 
v___x_103_ = lean_obj_once(&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0, &l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0);
v___x_104_ = l_StateRefT_x27_instMonad___redArg(v___x_103_);
v_toApplicative_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v___x_104_, 1);
lean_dec(v_unused_167_);
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_166_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_toApplicative_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_166_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_toFunctor_109_; lean_object* v_toSeq_110_; lean_object* v_toSeqLeft_111_; lean_object* v_toSeqRight_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_164_; 
v_toFunctor_109_ = lean_ctor_get(v_toApplicative_105_, 0);
v_toSeq_110_ = lean_ctor_get(v_toApplicative_105_, 2);
v_toSeqLeft_111_ = lean_ctor_get(v_toApplicative_105_, 3);
v_toSeqRight_112_ = lean_ctor_get(v_toApplicative_105_, 4);
v_isSharedCheck_164_ = !lean_is_exclusive(v_toApplicative_105_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_toApplicative_105_, 1);
lean_dec(v_unused_165_);
v___x_114_ = v_toApplicative_105_;
v_isShared_115_ = v_isSharedCheck_164_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_toSeqRight_112_);
lean_inc(v_toSeqLeft_111_);
lean_inc(v_toSeq_110_);
lean_inc(v_toFunctor_109_);
lean_dec(v_toApplicative_105_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_164_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___f_123_; lean_object* v___x_125_; 
v___f_116_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1));
v___f_117_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_109_);
v___f_118_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_118_, 0, v_toFunctor_109_);
v___f_119_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_119_, 0, v_toFunctor_109_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___f_118_);
lean_ctor_set(v___x_120_, 1, v___f_119_);
v___f_121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_121_, 0, v_toSeqRight_112_);
v___f_122_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_122_, 0, v_toSeqLeft_111_);
v___f_123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_123_, 0, v_toSeq_110_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 4, v___f_121_);
lean_ctor_set(v___x_114_, 3, v___f_122_);
lean_ctor_set(v___x_114_, 2, v___f_123_);
lean_ctor_set(v___x_114_, 1, v___f_116_);
lean_ctor_set(v___x_114_, 0, v___x_120_);
v___x_125_ = v___x_114_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___f_116_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v___f_123_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v___f_122_);
lean_ctor_set(v_reuseFailAlloc_163_, 4, v___f_121_);
v___x_125_ = v_reuseFailAlloc_163_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___f_117_);
lean_ctor_set(v___x_107_, 0, v___x_125_);
v___x_127_ = v___x_107_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___f_117_);
v___x_127_ = v_reuseFailAlloc_162_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v_toApplicative_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_160_; 
v___x_128_ = l_StateRefT_x27_instMonad___redArg(v___x_127_);
v_toApplicative_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_128_, 1);
lean_dec(v_unused_161_);
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_160_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_toApplicative_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_160_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_toFunctor_133_; lean_object* v_toSeq_134_; lean_object* v_toSeqLeft_135_; lean_object* v_toSeqRight_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_158_; 
v_toFunctor_133_ = lean_ctor_get(v_toApplicative_129_, 0);
v_toSeq_134_ = lean_ctor_get(v_toApplicative_129_, 2);
v_toSeqLeft_135_ = lean_ctor_get(v_toApplicative_129_, 3);
v_toSeqRight_136_ = lean_ctor_get(v_toApplicative_129_, 4);
v_isSharedCheck_158_ = !lean_is_exclusive(v_toApplicative_129_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_toApplicative_129_, 1);
lean_dec(v_unused_159_);
v___x_138_ = v_toApplicative_129_;
v_isShared_139_ = v_isSharedCheck_158_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_toSeqRight_136_);
lean_inc(v_toSeqLeft_135_);
lean_inc(v_toSeq_134_);
lean_inc(v_toFunctor_133_);
lean_dec(v_toApplicative_129_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_158_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_149_; 
v___f_140_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3));
v___f_141_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_133_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_142_, 0, v_toFunctor_133_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_143_, 0, v_toFunctor_133_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___f_142_);
lean_ctor_set(v___x_144_, 1, v___f_143_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_145_, 0, v_toSeqRight_136_);
v___f_146_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_146_, 0, v_toSeqLeft_135_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeq_134_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 4, v___f_145_);
lean_ctor_set(v___x_138_, 3, v___f_146_);
lean_ctor_set(v___x_138_, 2, v___f_147_);
lean_ctor_set(v___x_138_, 1, v___f_140_);
lean_ctor_set(v___x_138_, 0, v___x_144_);
v___x_149_ = v___x_138_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___f_140_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v___f_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v___f_146_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v___f_145_);
v___x_149_ = v_reuseFailAlloc_157_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___f_141_);
lean_ctor_set(v___x_131_, 0, v___x_149_);
v___x_151_ = v___x_131_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___f_141_);
v___x_151_ = v_reuseFailAlloc_156_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_1361__overap_154_; lean_object* v___x_155_; 
v___x_152_ = l_Lean_instInhabitedLocalContext_default;
v___x_153_ = l_instInhabitedOfMonad___redArg(v___x_151_, v___x_152_);
v___x_1361__overap_154_ = lean_panic_fn_borrowed(v___x_153_, v_msg_97_);
lean_dec(v___x_153_);
lean_inc(v___y_101_);
lean_inc_ref(v___y_100_);
lean_inc(v___y_99_);
lean_inc_ref(v___y_98_);
v___x_155_ = lean_apply_5(v___x_1361__overap_154_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, lean_box(0));
return v___x_155_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___boxed(lean_object* v_msg_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v_msg_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(lean_object* v_t_175_, lean_object* v_k_176_){
_start:
{
if (lean_obj_tag(v_t_175_) == 0)
{
lean_object* v_k_177_; lean_object* v_v_178_; lean_object* v_l_179_; lean_object* v_r_180_; uint8_t v___x_181_; 
v_k_177_ = lean_ctor_get(v_t_175_, 1);
v_v_178_ = lean_ctor_get(v_t_175_, 2);
v_l_179_ = lean_ctor_get(v_t_175_, 3);
v_r_180_ = lean_ctor_get(v_t_175_, 4);
v___x_181_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_176_, v_k_177_);
switch(v___x_181_)
{
case 0:
{
v_t_175_ = v_l_179_;
goto _start;
}
case 1:
{
lean_object* v___x_183_; 
lean_inc(v_v_178_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_v_178_);
return v___x_183_;
}
default: 
{
v_t_175_ = v_r_180_;
goto _start;
}
}
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg___boxed(lean_object* v_t_186_, lean_object* v_k_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_186_, v_k_187_);
lean_dec(v_k_187_);
lean_dec(v_t_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(lean_object* v_auxDeclToFullName_193_, lean_object* v_as_194_, size_t v_i_195_, size_t v_stop_196_, lean_object* v_b_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_a_204_; uint8_t v___x_208_; 
v___x_208_ = lean_usize_dec_eq(v_i_195_, v_stop_196_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_array_uget_borrowed(v_as_194_, v_i_195_);
if (lean_obj_tag(v___x_209_) == 0)
{
v_a_204_ = v_b_197_;
goto v___jp_203_;
}
else
{
lean_object* v_val_210_; 
v_val_210_ = lean_ctor_get(v___x_209_, 0);
if (lean_obj_tag(v_val_210_) == 0)
{
uint8_t v_kind_211_; 
v_kind_211_ = lean_ctor_get_uint8(v_val_210_, sizeof(void*)*4 + 1);
if (v_kind_211_ == 2)
{
lean_object* v_fvarId_212_; lean_object* v_userName_213_; lean_object* v_type_214_; lean_object* v___x_215_; 
v_fvarId_212_ = lean_ctor_get(v_val_210_, 1);
v_userName_213_ = lean_ctor_get(v_val_210_, 2);
v_type_214_ = lean_ctor_get(v_val_210_, 3);
lean_inc_ref(v_type_214_);
v___x_215_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_214_, v___y_199_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_217_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_auxDeclToFullName_193_, v_fvarId_212_);
if (lean_obj_tag(v___x_217_) == 1)
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_217_, 1);
lean_inc(v_userName_213_);
lean_inc(v_fvarId_212_);
v___x_219_ = l_Lean_LocalContext_mkAuxDecl(v_b_197_, v_fvarId_212_, v_userName_213_, v_a_216_, v_val_218_);
v_a_204_ = v___x_219_;
goto v___jp_203_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v___x_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_b_197_);
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0));
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1));
v___x_222_ = lean_unsigned_to_nat(635u);
v___x_223_ = lean_unsigned_to_nat(12u);
v___x_224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2));
v___x_225_ = 1;
lean_inc(v_userName_213_);
v___x_226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_213_, v___x_225_);
v___x_227_ = lean_string_append(v___x_224_, v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3));
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
v___x_230_ = l_mkPanicMessageWithDecl(v___x_220_, v___x_221_, v___x_222_, v___x_223_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v___x_230_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v_a_204_ = v_a_232_;
goto v___jp_203_;
}
else
{
return v___x_231_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_b_197_);
v_a_233_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_215_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_215_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v_fvarId_241_; lean_object* v_userName_242_; lean_object* v_type_243_; uint8_t v_bi_244_; lean_object* v___x_245_; 
v_fvarId_241_ = lean_ctor_get(v_val_210_, 1);
v_userName_242_ = lean_ctor_get(v_val_210_, 2);
v_type_243_ = lean_ctor_get(v_val_210_, 3);
v_bi_244_ = lean_ctor_get_uint8(v_val_210_, sizeof(void*)*4);
lean_inc_ref(v_type_243_);
v___x_245_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_243_, v___y_199_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
lean_inc(v_userName_242_);
lean_inc(v_fvarId_241_);
v___x_247_ = l_Lean_LocalContext_mkLocalDecl(v_b_197_, v_fvarId_241_, v_userName_242_, v_a_246_, v_bi_244_, v_kind_211_);
v_a_204_ = v___x_247_;
goto v___jp_203_;
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v_b_197_);
v_a_248_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_245_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
else
{
lean_object* v_fvarId_256_; lean_object* v_userName_257_; lean_object* v_type_258_; lean_object* v_value_259_; uint8_t v_nondep_260_; uint8_t v_kind_261_; lean_object* v___x_262_; 
v_fvarId_256_ = lean_ctor_get(v_val_210_, 1);
v_userName_257_ = lean_ctor_get(v_val_210_, 2);
v_type_258_ = lean_ctor_get(v_val_210_, 3);
v_value_259_ = lean_ctor_get(v_val_210_, 4);
v_nondep_260_ = lean_ctor_get_uint8(v_val_210_, sizeof(void*)*5);
v_kind_261_ = lean_ctor_get_uint8(v_val_210_, sizeof(void*)*5 + 1);
lean_inc_ref(v_type_258_);
v___x_262_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_258_, v___y_199_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
lean_inc_ref(v_value_259_);
v___x_264_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_value_259_, v___y_199_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
lean_inc(v_userName_257_);
lean_inc(v_fvarId_256_);
v___x_266_ = l_Lean_LocalContext_mkLetDecl(v_b_197_, v_fvarId_256_, v_userName_257_, v_a_263_, v_a_265_, v_nondep_260_, v_kind_261_);
v_a_204_ = v___x_266_;
goto v___jp_203_;
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_a_263_);
lean_dec_ref(v_b_197_);
v_a_267_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_264_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_264_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_b_197_);
v_a_275_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_262_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_262_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
else
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v_b_197_);
return v___x_283_;
}
v___jp_203_:
{
size_t v___x_205_; size_t v___x_206_; 
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_add(v_i_195_, v___x_205_);
v_i_195_ = v___x_206_;
v_b_197_ = v_a_204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___boxed(lean_object* v_auxDeclToFullName_284_, lean_object* v_as_285_, lean_object* v_i_286_, lean_object* v_stop_287_, lean_object* v_b_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
size_t v_i_boxed_294_; size_t v_stop_boxed_295_; lean_object* v_res_296_; 
v_i_boxed_294_ = lean_unbox_usize(v_i_286_);
lean_dec(v_i_286_);
v_stop_boxed_295_ = lean_unbox_usize(v_stop_287_);
lean_dec(v_stop_287_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_284_, v_as_285_, v_i_boxed_294_, v_stop_boxed_295_, v_b_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec_ref(v_as_285_);
lean_dec(v_auxDeclToFullName_284_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(lean_object* v_auxDeclToFullName_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v_cs_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_325_; 
v_cs_305_ = lean_ctor_get(v_x_298_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_325_ == 0)
{
v___x_307_ = v_x_298_;
v_isShared_308_ = v_isSharedCheck_325_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_cs_305_);
lean_dec(v_x_298_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_325_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_get_size(v_cs_305_);
v___x_311_ = lean_nat_dec_lt(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_313_; 
lean_dec_ref(v_cs_305_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v_x_299_);
v___x_313_ = v___x_307_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_x_299_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
uint8_t v___x_315_; 
v___x_315_ = lean_nat_dec_le(v___x_310_, v___x_310_);
if (v___x_315_ == 0)
{
if (v___x_311_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref(v_cs_305_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v_x_299_);
v___x_317_ = v___x_307_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_x_299_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
lean_del_object(v___x_307_);
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_310_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_297_, v_cs_305_, v___x_319_, v___x_320_, v_x_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec_ref(v_cs_305_);
return v___x_321_;
}
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
lean_del_object(v___x_307_);
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_310_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_297_, v_cs_305_, v___x_322_, v___x_323_, v_x_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec_ref(v_cs_305_);
return v___x_324_;
}
}
}
}
else
{
lean_object* v_vs_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_346_; 
v_vs_326_ = lean_ctor_get(v_x_298_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_346_ == 0)
{
v___x_328_ = v_x_298_;
v_isShared_329_ = v_isSharedCheck_346_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_vs_326_);
lean_dec(v_x_298_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_346_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_array_get_size(v_vs_326_);
v___x_332_ = lean_nat_dec_lt(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_334_; 
lean_dec_ref(v_vs_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 0);
lean_ctor_set(v___x_328_, 0, v_x_299_);
v___x_334_ = v___x_328_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_x_299_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
else
{
uint8_t v___x_336_; 
v___x_336_ = lean_nat_dec_le(v___x_331_, v___x_331_);
if (v___x_336_ == 0)
{
if (v___x_332_ == 0)
{
lean_object* v___x_338_; 
lean_dec_ref(v_vs_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 0);
lean_ctor_set(v___x_328_, 0, v_x_299_);
v___x_338_ = v___x_328_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_x_299_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
lean_del_object(v___x_328_);
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_331_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_297_, v_vs_326_, v___x_340_, v___x_341_, v_x_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec_ref(v_vs_326_);
return v___x_342_;
}
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
lean_del_object(v___x_328_);
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_331_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_297_, v_vs_326_, v___x_343_, v___x_344_, v_x_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec_ref(v_vs_326_);
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_347_, lean_object* v_as_348_, size_t v_i_349_, size_t v_stop_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_eq(v_i_349_, v_stop_350_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_array_uget_borrowed(v_as_348_, v_i_349_);
lean_inc(v___x_358_);
v___x_359_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_347_, v___x_358_, v_b_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; size_t v___x_361_; size_t v___x_362_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_349_, v___x_361_);
v_i_349_ = v___x_362_;
v_b_351_ = v_a_360_;
goto _start;
}
else
{
return v___x_359_;
}
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_b_351_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_365_, lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_stop_368_, lean_object* v_b_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_368_);
lean_dec(v_stop_368_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_365_, v_as_366_, v_i_boxed_375_, v_stop_boxed_376_, v_b_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec_ref(v_as_366_);
lean_dec(v_auxDeclToFullName_365_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_auxDeclToFullName_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_378_, v_x_379_, v_x_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v_auxDeclToFullName_378_);
return v_res_386_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(lean_object* v_auxDeclToFullName_388_, lean_object* v_x_389_, size_t v_x_390_, size_t v_x_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v_cs_398_; lean_object* v___x_399_; size_t v___x_400_; lean_object* v_j_401_; lean_object* v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; 
v_cs_398_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_cs_398_);
lean_dec_ref_known(v_x_389_, 1);
v___x_399_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0);
v___x_400_ = lean_usize_shift_right(v_x_390_, v_x_391_);
v_j_401_ = lean_usize_to_nat(v___x_400_);
v___x_402_ = lean_array_get_borrowed(v___x_399_, v_cs_398_, v_j_401_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_shift_left(v___x_403_, v_x_391_);
v___x_405_ = lean_usize_sub(v___x_404_, v___x_403_);
v___x_406_ = lean_usize_land(v_x_390_, v___x_405_);
v___x_407_ = ((size_t)5ULL);
v___x_408_ = lean_usize_sub(v_x_391_, v___x_407_);
lean_inc(v___x_402_);
v___x_409_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_388_, v___x_402_, v___x_406_, v___x_408_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_add(v_j_401_, v___x_411_);
lean_dec(v_j_401_);
v___x_413_ = lean_array_get_size(v_cs_398_);
v___x_414_ = lean_nat_dec_lt(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_dec(v___x_412_);
lean_dec(v_a_410_);
lean_dec_ref(v_cs_398_);
return v___x_409_;
}
else
{
uint8_t v___x_415_; 
v___x_415_ = lean_nat_dec_le(v___x_413_, v___x_413_);
if (v___x_415_ == 0)
{
if (v___x_414_ == 0)
{
lean_dec(v___x_412_);
lean_dec(v_a_410_);
lean_dec_ref(v_cs_398_);
return v___x_409_;
}
else
{
size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
lean_dec_ref_known(v___x_409_, 1);
v___x_416_ = lean_usize_of_nat(v___x_412_);
lean_dec(v___x_412_);
v___x_417_ = lean_usize_of_nat(v___x_413_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_388_, v_cs_398_, v___x_416_, v___x_417_, v_a_410_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec_ref(v_cs_398_);
return v___x_418_;
}
}
else
{
size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
lean_dec_ref_known(v___x_409_, 1);
v___x_419_ = lean_usize_of_nat(v___x_412_);
lean_dec(v___x_412_);
v___x_420_ = lean_usize_of_nat(v___x_413_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_388_, v_cs_398_, v___x_419_, v___x_420_, v_a_410_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec_ref(v_cs_398_);
return v___x_421_;
}
}
}
else
{
lean_dec(v_j_401_);
lean_dec_ref(v_cs_398_);
return v___x_409_;
}
}
else
{
lean_object* v_vs_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_442_; 
v_vs_422_ = lean_ctor_get(v_x_389_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_389_);
if (v_isSharedCheck_442_ == 0)
{
v___x_424_ = v_x_389_;
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_vs_422_);
lean_dec(v_x_389_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_usize_to_nat(v_x_390_);
v___x_427_ = lean_array_get_size(v_vs_422_);
v___x_428_ = lean_nat_dec_lt(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v___x_426_);
lean_dec_ref(v_vs_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
lean_ctor_set(v___x_424_, 0, v_x_392_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_x_392_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_le(v___x_427_, v___x_427_);
if (v___x_432_ == 0)
{
if (v___x_428_ == 0)
{
lean_object* v___x_434_; 
lean_dec(v___x_426_);
lean_dec_ref(v_vs_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
lean_ctor_set(v___x_424_, 0, v_x_392_);
v___x_434_ = v___x_424_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_x_392_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
else
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
lean_del_object(v___x_424_);
v___x_436_ = lean_usize_of_nat(v___x_426_);
lean_dec(v___x_426_);
v___x_437_ = lean_usize_of_nat(v___x_427_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_388_, v_vs_422_, v___x_436_, v___x_437_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec_ref(v_vs_422_);
return v___x_438_;
}
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
lean_del_object(v___x_424_);
v___x_439_ = lean_usize_of_nat(v___x_426_);
lean_dec(v___x_426_);
v___x_440_ = lean_usize_of_nat(v___x_427_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_388_, v_vs_422_, v___x_439_, v___x_440_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec_ref(v_vs_422_);
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
size_t v_x_4508__boxed_453_; size_t v_x_4509__boxed_454_; lean_object* v_res_455_; 
v_x_4508__boxed_453_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_x_4509__boxed_454_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_res_455_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_443_, v_x_444_, v_x_4508__boxed_453_, v_x_4509__boxed_454_, v_x_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v_auxDeclToFullName_443_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(lean_object* v_auxDeclToFullName_456_, lean_object* v_t_457_, lean_object* v_init_458_, lean_object* v_start_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_nat_dec_eq(v_start_459_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v_root_467_; lean_object* v_tail_468_; size_t v_shift_469_; lean_object* v_tailOff_470_; uint8_t v___x_471_; 
v_root_467_ = lean_ctor_get(v_t_457_, 0);
lean_inc_ref(v_root_467_);
v_tail_468_ = lean_ctor_get(v_t_457_, 1);
lean_inc_ref(v_tail_468_);
v_shift_469_ = lean_ctor_get_usize(v_t_457_, 4);
v_tailOff_470_ = lean_ctor_get(v_t_457_, 3);
lean_inc(v_tailOff_470_);
lean_dec_ref(v_t_457_);
v___x_471_ = lean_nat_dec_le(v_tailOff_470_, v_start_459_);
if (v___x_471_ == 0)
{
size_t v___x_472_; lean_object* v___x_473_; 
lean_dec(v_tailOff_470_);
v___x_472_ = lean_usize_of_nat(v_start_459_);
v___x_473_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_456_, v_root_467_, v___x_472_, v_shift_469_, v_init_458_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
v___x_475_ = lean_array_get_size(v_tail_468_);
v___x_476_ = lean_nat_dec_lt(v___x_465_, v___x_475_);
if (v___x_476_ == 0)
{
lean_dec(v_a_474_);
lean_dec_ref(v_tail_468_);
return v___x_473_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_le(v___x_475_, v___x_475_);
if (v___x_477_ == 0)
{
if (v___x_476_ == 0)
{
lean_dec(v_a_474_);
lean_dec_ref(v_tail_468_);
return v___x_473_;
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
lean_dec_ref_known(v___x_473_, 1);
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_475_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_456_, v_tail_468_, v___x_478_, v___x_479_, v_a_474_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec_ref(v_tail_468_);
return v___x_480_;
}
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
lean_dec_ref_known(v___x_473_, 1);
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_475_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_456_, v_tail_468_, v___x_481_, v___x_482_, v_a_474_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec_ref(v_tail_468_);
return v___x_483_;
}
}
}
else
{
lean_dec_ref(v_tail_468_);
return v___x_473_;
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
lean_dec_ref(v_root_467_);
v___x_484_ = lean_nat_sub(v_start_459_, v_tailOff_470_);
lean_dec(v_tailOff_470_);
v___x_485_ = lean_array_get_size(v_tail_468_);
v___x_486_ = lean_nat_dec_lt(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v___x_484_);
lean_dec_ref(v_tail_468_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_init_458_);
return v___x_487_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = lean_nat_dec_le(v___x_485_, v___x_485_);
if (v___x_488_ == 0)
{
if (v___x_486_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v___x_484_);
lean_dec_ref(v_tail_468_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_init_458_);
return v___x_489_;
}
else
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_usize_of_nat(v___x_484_);
lean_dec(v___x_484_);
v___x_491_ = lean_usize_of_nat(v___x_485_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_456_, v_tail_468_, v___x_490_, v___x_491_, v_init_458_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec_ref(v_tail_468_);
return v___x_492_;
}
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_usize_of_nat(v___x_484_);
lean_dec(v___x_484_);
v___x_494_ = lean_usize_of_nat(v___x_485_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_456_, v_tail_468_, v___x_493_, v___x_494_, v_init_458_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec_ref(v_tail_468_);
return v___x_495_;
}
}
}
}
else
{
lean_object* v_root_496_; lean_object* v_tail_497_; lean_object* v___x_498_; 
v_root_496_ = lean_ctor_get(v_t_457_, 0);
lean_inc_ref(v_root_496_);
v_tail_497_ = lean_ctor_get(v_t_457_, 1);
lean_inc_ref(v_tail_497_);
lean_dec_ref(v_t_457_);
v___x_498_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_456_, v_root_496_, v_init_458_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
v___x_500_ = lean_array_get_size(v_tail_497_);
v___x_501_ = lean_nat_dec_lt(v___x_465_, v___x_500_);
if (v___x_501_ == 0)
{
lean_dec(v_a_499_);
lean_dec_ref(v_tail_497_);
return v___x_498_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = lean_nat_dec_le(v___x_500_, v___x_500_);
if (v___x_502_ == 0)
{
if (v___x_501_ == 0)
{
lean_dec(v_a_499_);
lean_dec_ref(v_tail_497_);
return v___x_498_;
}
else
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
lean_dec_ref_known(v___x_498_, 1);
v___x_503_ = ((size_t)0ULL);
v___x_504_ = lean_usize_of_nat(v___x_500_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_456_, v_tail_497_, v___x_503_, v___x_504_, v_a_499_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec_ref(v_tail_497_);
return v___x_505_;
}
}
else
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
lean_dec_ref_known(v___x_498_, 1);
v___x_506_ = ((size_t)0ULL);
v___x_507_ = lean_usize_of_nat(v___x_500_);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_456_, v_tail_497_, v___x_506_, v___x_507_, v_a_499_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec_ref(v_tail_497_);
return v___x_508_;
}
}
}
else
{
lean_dec_ref(v_tail_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3___boxed(lean_object* v_auxDeclToFullName_509_, lean_object* v_t_510_, lean_object* v_init_511_, lean_object* v_start_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_509_, v_t_510_, v_init_511_, v_start_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v_start_512_);
lean_dec(v_auxDeclToFullName_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(lean_object* v_auxDeclToFullName_519_, lean_object* v_lctx_520_, lean_object* v_init_521_, lean_object* v_start_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_decls_528_; lean_object* v___x_529_; 
v_decls_528_ = lean_ctor_get(v_lctx_520_, 1);
lean_inc_ref(v_decls_528_);
lean_dec_ref(v_lctx_520_);
v___x_529_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_519_, v_decls_528_, v_init_521_, v_start_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2___boxed(lean_object* v_auxDeclToFullName_530_, lean_object* v_lctx_531_, lean_object* v_init_532_, lean_object* v_start_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_530_, v_lctx_531_, v_init_532_, v_start_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v_start_533_);
lean_dec(v_auxDeclToFullName_530_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_540_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_unsigned_to_nat(32u);
v___x_544_ = lean_mk_empty_array_with_capacity(v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3(void){
_start:
{
size_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_546_ = ((size_t)5ULL);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_unsigned_to_nat(32u);
v___x_549_ = lean_mk_empty_array_with_capacity(v___x_548_);
v___x_550_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2);
v___x_551_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___x_549_);
lean_ctor_set(v___x_551_, 2, v___x_547_);
lean_ctor_set(v___x_551_, 3, v___x_547_);
lean_ctor_set_usize(v___x_551_, 4, v___x_546_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_box(1);
v___x_553_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3);
v___x_554_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1);
v___x_555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
lean_ctor_set(v___x_555_, 2, v___x_552_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(lean_object* v_lctx_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_auxDeclToFullName_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_auxDeclToFullName_562_ = lean_ctor_get(v_lctx_556_, 2);
lean_inc(v_auxDeclToFullName_562_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4);
v___x_565_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_562_, v_lctx_556_, v___x_564_, v___x_563_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v_auxDeclToFullName_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___boxed(lean_object* v_lctx_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_ks_577_; lean_object* v_vs_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_602_; 
v_ks_577_ = lean_ctor_get(v_x_573_, 0);
v_vs_578_ = lean_ctor_get(v_x_573_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_602_ == 0)
{
v___x_580_ = v_x_573_;
v_isShared_581_ = v_isSharedCheck_602_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_vs_578_);
lean_inc(v_ks_577_);
lean_dec(v_x_573_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_602_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_array_get_size(v_ks_577_);
v___x_583_ = lean_nat_dec_lt(v_x_574_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
lean_dec(v_x_574_);
v___x_584_ = lean_array_push(v_ks_577_, v_x_575_);
v___x_585_ = lean_array_push(v_vs_578_, v_x_576_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_585_);
lean_ctor_set(v___x_580_, 0, v___x_584_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v_k_x27_589_; uint8_t v___x_590_; 
v_k_x27_589_ = lean_array_fget_borrowed(v_ks_577_, v_x_574_);
v___x_590_ = l_Lean_instBEqMVarId_beq(v_x_575_, v_k_x27_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_592_; 
if (v_isShared_581_ == 0)
{
v___x_592_ = v___x_580_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_ks_577_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_vs_578_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_x_574_, v___x_593_);
lean_dec(v_x_574_);
v_x_573_ = v___x_592_;
v_x_574_ = v___x_594_;
goto _start;
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_597_ = lean_array_fset(v_ks_577_, v_x_574_, v_x_575_);
v___x_598_ = lean_array_fset(v_vs_578_, v_x_574_, v_x_576_);
lean_dec(v_x_574_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_598_);
lean_ctor_set(v___x_580_, 0, v___x_597_);
v___x_600_ = v___x_580_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(lean_object* v_n_603_, lean_object* v_k_604_, lean_object* v_v_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_n_603_, v___x_606_, v_k_604_, v_v_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(lean_object* v_x_609_, size_t v_x_610_, size_t v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_object* v_es_614_; size_t v___x_615_; size_t v___x_616_; lean_object* v_j_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_es_614_ = lean_ctor_get(v_x_609_, 0);
v___x_615_ = ((size_t)31ULL);
v___x_616_ = lean_usize_land(v_x_610_, v___x_615_);
v_j_617_ = lean_usize_to_nat(v___x_616_);
v___x_618_ = lean_array_get_size(v_es_614_);
v___x_619_ = lean_nat_dec_lt(v_j_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_dec(v_j_617_);
lean_dec(v_x_613_);
lean_dec(v_x_612_);
return v_x_609_;
}
else
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_658_; 
lean_inc_ref(v_es_614_);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_609_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_x_609_, 0);
lean_dec(v_unused_659_);
v___x_621_ = v_x_609_;
v_isShared_622_ = v_isSharedCheck_658_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_x_609_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_658_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_v_623_; lean_object* v___x_624_; lean_object* v_xs_x27_625_; lean_object* v___y_627_; 
v_v_623_ = lean_array_fget(v_es_614_, v_j_617_);
v___x_624_ = lean_box(0);
v_xs_x27_625_ = lean_array_fset(v_es_614_, v_j_617_, v___x_624_);
switch(lean_obj_tag(v_v_623_))
{
case 0:
{
lean_object* v_key_632_; lean_object* v_val_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_643_; 
v_key_632_ = lean_ctor_get(v_v_623_, 0);
v_val_633_ = lean_ctor_get(v_v_623_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_v_623_);
if (v_isSharedCheck_643_ == 0)
{
v___x_635_ = v_v_623_;
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_val_633_);
lean_inc(v_key_632_);
lean_dec(v_v_623_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
uint8_t v___x_637_; 
v___x_637_ = l_Lean_instBEqMVarId_beq(v_x_612_, v_key_632_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_del_object(v___x_635_);
v___x_638_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_632_, v_val_633_, v_x_612_, v_x_613_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___y_627_ = v___x_639_;
goto v___jp_626_;
}
else
{
lean_object* v___x_641_; 
lean_dec(v_val_633_);
lean_dec(v_key_632_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v_x_613_);
lean_ctor_set(v___x_635_, 0, v_x_612_);
v___x_641_ = v___x_635_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_x_612_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_x_613_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
}
}
}
case 1:
{
lean_object* v_node_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_656_; 
v_node_644_ = lean_ctor_get(v_v_623_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v_v_623_);
if (v_isSharedCheck_656_ == 0)
{
v___x_646_ = v_v_623_;
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_node_644_);
lean_dec(v_v_623_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_648_ = ((size_t)5ULL);
v___x_649_ = lean_usize_shift_right(v_x_610_, v___x_648_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_x_611_, v___x_650_);
v___x_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_node_644_, v___x_649_, v___x_651_, v_x_612_, v_x_613_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_652_);
v___x_654_ = v___x_646_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
v___y_627_ = v___x_654_;
goto v___jp_626_;
}
}
}
default: 
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_x_612_);
lean_ctor_set(v___x_657_, 1, v_x_613_);
v___y_627_ = v___x_657_;
goto v___jp_626_;
}
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_array_fset(v_xs_x27_625_, v_j_617_, v___y_627_);
lean_dec(v_j_617_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_628_);
v___x_630_ = v___x_621_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
lean_object* v_ks_660_; lean_object* v_vs_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_681_; 
v_ks_660_ = lean_ctor_get(v_x_609_, 0);
v_vs_661_ = lean_ctor_get(v_x_609_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_609_);
if (v_isSharedCheck_681_ == 0)
{
v___x_663_ = v_x_609_;
v_isShared_664_ = v_isSharedCheck_681_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_vs_661_);
lean_inc(v_ks_660_);
lean_dec(v_x_609_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_681_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_ks_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_vs_661_);
v___x_666_ = v_reuseFailAlloc_680_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v_newNode_667_; uint8_t v___y_669_; size_t v___x_675_; uint8_t v___x_676_; 
v_newNode_667_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v___x_666_, v_x_612_, v_x_613_);
v___x_675_ = ((size_t)7ULL);
v___x_676_ = lean_usize_dec_le(v___x_675_, v_x_611_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_677_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_667_);
v___x_678_ = lean_unsigned_to_nat(4u);
v___x_679_ = lean_nat_dec_lt(v___x_677_, v___x_678_);
lean_dec(v___x_677_);
v___y_669_ = v___x_679_;
goto v___jp_668_;
}
else
{
v___y_669_ = v___x_676_;
goto v___jp_668_;
}
v___jp_668_:
{
if (v___y_669_ == 0)
{
lean_object* v_ks_670_; lean_object* v_vs_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_ks_670_ = lean_ctor_get(v_newNode_667_, 0);
lean_inc_ref(v_ks_670_);
v_vs_671_ = lean_ctor_get(v_newNode_667_, 1);
lean_inc_ref(v_vs_671_);
lean_dec_ref(v_newNode_667_);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0);
v___x_674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_x_611_, v_ks_670_, v_vs_671_, v___x_672_, v___x_673_);
lean_dec_ref(v_vs_671_);
lean_dec_ref(v_ks_670_);
return v___x_674_;
}
else
{
return v_newNode_667_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(size_t v_depth_682_, lean_object* v_keys_683_, lean_object* v_vals_684_, lean_object* v_i_685_, lean_object* v_entries_686_){
_start:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_array_get_size(v_keys_683_);
v___x_688_ = lean_nat_dec_lt(v_i_685_, v___x_687_);
if (v___x_688_ == 0)
{
lean_dec(v_i_685_);
return v_entries_686_;
}
else
{
lean_object* v_k_689_; lean_object* v_v_690_; uint64_t v___x_691_; size_t v_h_692_; size_t v___x_693_; lean_object* v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v_h_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_k_689_ = lean_array_fget_borrowed(v_keys_683_, v_i_685_);
v_v_690_ = lean_array_fget_borrowed(v_vals_684_, v_i_685_);
v___x_691_ = l_Lean_instHashableMVarId_hash(v_k_689_);
v_h_692_ = lean_uint64_to_usize(v___x_691_);
v___x_693_ = ((size_t)5ULL);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_sub(v_depth_682_, v___x_695_);
v___x_697_ = lean_usize_mul(v___x_693_, v___x_696_);
v_h_698_ = lean_usize_shift_right(v_h_692_, v___x_697_);
v___x_699_ = lean_nat_add(v_i_685_, v___x_694_);
lean_dec(v_i_685_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
v___x_700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_entries_686_, v_h_698_, v_depth_682_, v_k_689_, v_v_690_);
v_i_685_ = v___x_699_;
v_entries_686_ = v___x_700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg___boxed(lean_object* v_depth_702_, lean_object* v_keys_703_, lean_object* v_vals_704_, lean_object* v_i_705_, lean_object* v_entries_706_){
_start:
{
size_t v_depth_boxed_707_; lean_object* v_res_708_; 
v_depth_boxed_707_ = lean_unbox_usize(v_depth_702_);
lean_dec(v_depth_702_);
v_res_708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_boxed_707_, v_keys_703_, v_vals_704_, v_i_705_, v_entries_706_);
lean_dec_ref(v_vals_704_);
lean_dec_ref(v_keys_703_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
size_t v_x_4882__boxed_714_; size_t v_x_4883__boxed_715_; lean_object* v_res_716_; 
v_x_4882__boxed_714_ = lean_unbox_usize(v_x_710_);
lean_dec(v_x_710_);
v_x_4883__boxed_715_ = lean_unbox_usize(v_x_711_);
lean_dec(v_x_711_);
v_res_716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_709_, v_x_4882__boxed_714_, v_x_4883__boxed_715_, v_x_712_, v_x_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
uint64_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_720_ = l_Lean_instHashableMVarId_hash(v_x_718_);
v___x_721_ = lean_uint64_to_usize(v___x_720_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_717_, v___x_721_, v___x_722_, v_x_718_, v_x_719_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(lean_object* v_mvarId_724_, lean_object* v_val_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; lean_object* v_mctx_729_; lean_object* v_cache_730_; lean_object* v_zetaDeltaFVarIds_731_; lean_object* v_postponed_732_; lean_object* v_diag_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_761_; 
v___x_728_ = lean_st_ref_take(v___y_726_);
v_mctx_729_ = lean_ctor_get(v___x_728_, 0);
v_cache_730_ = lean_ctor_get(v___x_728_, 1);
v_zetaDeltaFVarIds_731_ = lean_ctor_get(v___x_728_, 2);
v_postponed_732_ = lean_ctor_get(v___x_728_, 3);
v_diag_733_ = lean_ctor_get(v___x_728_, 4);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_761_ == 0)
{
v___x_735_ = v___x_728_;
v_isShared_736_ = v_isSharedCheck_761_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_diag_733_);
lean_inc(v_postponed_732_);
lean_inc(v_zetaDeltaFVarIds_731_);
lean_inc(v_cache_730_);
lean_inc(v_mctx_729_);
lean_dec(v___x_728_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_761_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_depth_737_; lean_object* v_levelAssignDepth_738_; lean_object* v_lmvarCounter_739_; lean_object* v_mvarCounter_740_; lean_object* v_lDecls_741_; lean_object* v_decls_742_; lean_object* v_userNames_743_; lean_object* v_lAssignment_744_; lean_object* v_eAssignment_745_; lean_object* v_dAssignment_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_760_; 
v_depth_737_ = lean_ctor_get(v_mctx_729_, 0);
v_levelAssignDepth_738_ = lean_ctor_get(v_mctx_729_, 1);
v_lmvarCounter_739_ = lean_ctor_get(v_mctx_729_, 2);
v_mvarCounter_740_ = lean_ctor_get(v_mctx_729_, 3);
v_lDecls_741_ = lean_ctor_get(v_mctx_729_, 4);
v_decls_742_ = lean_ctor_get(v_mctx_729_, 5);
v_userNames_743_ = lean_ctor_get(v_mctx_729_, 6);
v_lAssignment_744_ = lean_ctor_get(v_mctx_729_, 7);
v_eAssignment_745_ = lean_ctor_get(v_mctx_729_, 8);
v_dAssignment_746_ = lean_ctor_get(v_mctx_729_, 9);
v_isSharedCheck_760_ = !lean_is_exclusive(v_mctx_729_);
if (v_isSharedCheck_760_ == 0)
{
v___x_748_ = v_mctx_729_;
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_dAssignment_746_);
lean_inc(v_eAssignment_745_);
lean_inc(v_lAssignment_744_);
lean_inc(v_userNames_743_);
lean_inc(v_decls_742_);
lean_inc(v_lDecls_741_);
lean_inc(v_mvarCounter_740_);
lean_inc(v_lmvarCounter_739_);
lean_inc(v_levelAssignDepth_738_);
lean_inc(v_depth_737_);
lean_dec(v_mctx_729_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_745_, v_mvarId_724_, v_val_725_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 8, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_depth_737_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_levelAssignDepth_738_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_lmvarCounter_739_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_mvarCounter_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_lDecls_741_);
lean_ctor_set(v_reuseFailAlloc_759_, 5, v_decls_742_);
lean_ctor_set(v_reuseFailAlloc_759_, 6, v_userNames_743_);
lean_ctor_set(v_reuseFailAlloc_759_, 7, v_lAssignment_744_);
lean_ctor_set(v_reuseFailAlloc_759_, 8, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_759_, 9, v_dAssignment_746_);
v___x_752_ = v_reuseFailAlloc_759_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_752_);
v___x_754_ = v___x_735_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_cache_730_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_zetaDeltaFVarIds_731_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_postponed_732_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_diag_733_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_st_ref_set(v___y_726_, v___x_754_);
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
size_t v_x_5242__boxed_880_; size_t v_x_5243__boxed_881_; lean_object* v_res_882_; 
v_x_5242__boxed_880_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_x_5243__boxed_881_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_res_882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_874_, v_x_875_, v_x_5242__boxed_880_, v_x_5243__boxed_881_, v_x_878_, v_x_879_);
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
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4));
v___x_1455_ = l_Lean_stringToMessageData(v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(lean_object* v_as_x27_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
if (lean_obj_tag(v_as_x27_1456_) == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1457_);
return v___x_1463_;
}
else
{
lean_object* v_head_1464_; lean_object* v_tail_1465_; lean_object* v___x_1466_; 
v_head_1464_ = lean_ctor_get(v_as_x27_1456_, 0);
v_tail_1465_ = lean_ctor_get(v_as_x27_1456_, 1);
lean_inc(v_head_1464_);
lean_inc(v_b_1457_);
v___x_1466_ = l_Lean_MVarId_clear(v_b_1457_, v_head_1464_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; 
lean_dec(v_b_1457_);
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v_as_x27_1456_ = v_tail_1465_;
v_b_1457_ = v_a_1467_;
goto _start;
}
else
{
lean_object* v_a_1469_; uint8_t v___y_1471_; uint8_t v___x_1512_; 
v_a_1469_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1469_);
v___x_1512_ = l_Lean_Exception_isInterrupt(v_a_1469_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; 
v___x_1513_ = l_Lean_Exception_isRuntime(v_a_1469_);
v___y_1471_ = v___x_1513_;
goto v___jp_1470_;
}
else
{
lean_dec(v_a_1469_);
v___y_1471_ = v___x_1512_;
goto v___jp_1470_;
}
v___jp_1470_:
{
if (v___y_1471_ == 0)
{
lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1510_; 
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v___x_1466_, 0);
lean_dec(v_unused_1511_);
v___x_1473_ = v___x_1466_;
v_isShared_1474_ = v_isSharedCheck_1510_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v___x_1466_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1510_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; 
lean_inc(v_head_1464_);
v___x_1475_ = l_Lean_FVarId_getDecl___redArg(v_head_1464_, v___y_1458_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; uint8_t v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = l_Lean_LocalDecl_isAuxDecl(v_a_1476_);
if (v___x_1477_ == 0)
{
lean_dec(v_a_1476_);
lean_del_object(v___x_1473_);
v_as_x27_1456_ = v_tail_1465_;
goto _start;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1479_ = l_Lean_LocalDecl_userName(v_a_1476_);
lean_dec(v_a_1476_);
v___x_1480_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_1481_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
v___x_1482_ = l_Lean_MessageData_ofName(v___x_1479_);
lean_inc_ref(v___x_1482_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v___x_1482_);
v___x_1487_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1488_);
v___x_1490_ = v___x_1473_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; 
lean_inc(v_b_1457_);
v___x_1491_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1480_, v_b_1457_, v___x_1490_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
v_as_x27_1456_ = v_tail_1465_;
goto _start;
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_b_1457_);
v_a_1493_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1491_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1491_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_del_object(v___x_1473_);
lean_dec(v_b_1457_);
v_a_1502_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1475_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1475_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_dec(v_b_1457_);
return v___x_1466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(lean_object* v_as_x27_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1514_, v_b_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v_as_x27_1514_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_1522_, size_t v_sz_1523_, size_t v_i_1524_, lean_object* v_b_1525_){
_start:
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_usize_dec_lt(v_i_1524_, v_sz_1523_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_b_1525_);
return v___x_1528_;
}
else
{
lean_object* v_snd_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1547_; 
v_snd_1529_ = lean_ctor_get(v_b_1525_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_b_1525_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_b_1525_, 0);
lean_dec(v_unused_1548_);
v___x_1531_ = v_b_1525_;
v_isShared_1532_ = v_isSharedCheck_1547_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_snd_1529_);
lean_dec(v_b_1525_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1547_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v_a_1535_; lean_object* v_a_1542_; 
v___x_1533_ = lean_box(0);
v_a_1542_ = lean_array_uget_borrowed(v_as_1522_, v_i_1524_);
if (lean_obj_tag(v_a_1542_) == 0)
{
v_a_1535_ = v_snd_1529_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1543_; uint8_t v___x_1544_; 
v_val_1543_ = lean_ctor_get(v_a_1542_, 0);
v___x_1544_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1543_);
if (v___x_1544_ == 0)
{
v_a_1535_ = v_snd_1529_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = l_Lean_LocalDecl_fvarId(v_val_1543_);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v_snd_1529_);
v_a_1535_ = v___x_1546_;
goto v___jp_1534_;
}
}
v___jp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v_a_1535_);
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1537_ = v___x_1531_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_a_1535_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
size_t v___x_1538_; size_t v___x_1539_; 
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1524_, v___x_1538_);
v_i_1524_ = v___x_1539_;
v_b_1525_ = v___x_1537_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_1549_, lean_object* v_sz_1550_, lean_object* v_i_1551_, lean_object* v_b_1552_, lean_object* v___y_1553_){
_start:
{
size_t v_sz_boxed_1554_; size_t v_i_boxed_1555_; lean_object* v_res_1556_; 
v_sz_boxed_1554_ = lean_unbox_usize(v_sz_1550_);
lean_dec(v_sz_1550_);
v_i_boxed_1555_ = lean_unbox_usize(v_i_1551_);
lean_dec(v_i_1551_);
v_res_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1549_, v_sz_boxed_1554_, v_i_boxed_1555_, v_b_1552_);
lean_dec_ref(v_as_1549_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(lean_object* v_as_1557_, size_t v_sz_1558_, size_t v_i_1559_, lean_object* v_b_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_usize_dec_lt(v_i_1559_, v_sz_1558_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_b_1560_);
return v___x_1567_;
}
else
{
lean_object* v_snd_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1586_; 
v_snd_1568_ = lean_ctor_get(v_b_1560_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_b_1560_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v_b_1560_, 0);
lean_dec(v_unused_1587_);
v___x_1570_ = v_b_1560_;
v_isShared_1571_ = v_isSharedCheck_1586_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_snd_1568_);
lean_dec(v_b_1560_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1586_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v_a_1574_; lean_object* v_a_1581_; 
v___x_1572_ = lean_box(0);
v_a_1581_ = lean_array_uget_borrowed(v_as_1557_, v_i_1559_);
if (lean_obj_tag(v_a_1581_) == 0)
{
v_a_1574_ = v_snd_1568_;
goto v___jp_1573_;
}
else
{
lean_object* v_val_1582_; uint8_t v___x_1583_; 
v_val_1582_ = lean_ctor_get(v_a_1581_, 0);
v___x_1583_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1582_);
if (v___x_1583_ == 0)
{
v_a_1574_ = v_snd_1568_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = l_Lean_LocalDecl_fvarId(v_val_1582_);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v_snd_1568_);
v_a_1574_ = v___x_1585_;
goto v___jp_1573_;
}
}
v___jp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v_a_1574_);
lean_ctor_set(v___x_1570_, 0, v___x_1572_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_a_1574_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = ((size_t)1ULL);
v___x_1578_ = lean_usize_add(v_i_1559_, v___x_1577_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1557_, v_sz_1558_, v___x_1578_, v___x_1576_);
return v___x_1579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1588_, lean_object* v_sz_1589_, lean_object* v_i_1590_, lean_object* v_b_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
size_t v_sz_boxed_1597_; size_t v_i_boxed_1598_; lean_object* v_res_1599_; 
v_sz_boxed_1597_ = lean_unbox_usize(v_sz_1589_);
lean_dec(v_sz_1589_);
v_i_boxed_1598_ = lean_unbox_usize(v_i_1590_);
lean_dec(v_i_1590_);
v_res_1599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_1588_, v_sz_boxed_1597_, v_i_boxed_1598_, v_b_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v_as_1588_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object* v_init_1600_, lean_object* v_n_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
if (lean_obj_tag(v_n_1601_) == 0)
{
lean_object* v_cs_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; size_t v_sz_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v_cs_1608_ = lean_ctor_get(v_n_1601_, 0);
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_b_1602_);
v_sz_1611_ = lean_array_size(v_cs_1608_);
v___x_1612_ = ((size_t)0ULL);
v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1600_, v_cs_1608_, v_sz_1611_, v___x_1612_, v___x_1610_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1628_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v_fst_1618_; 
v_fst_1618_ = lean_ctor_get(v_a_1614_, 0);
if (lean_obj_tag(v_fst_1618_) == 0)
{
lean_object* v_snd_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v_snd_1619_ = lean_ctor_get(v_a_1614_, 1);
lean_inc(v_snd_1619_);
lean_dec(v_a_1614_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_snd_1619_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1620_);
v___x_1622_ = v___x_1616_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
else
{
lean_object* v_val_1624_; lean_object* v___x_1626_; 
lean_inc_ref(v_fst_1618_);
lean_dec(v_a_1614_);
v_val_1624_ = lean_ctor_get(v_fst_1618_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v_fst_1618_, 1);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v_val_1624_);
v___x_1626_ = v___x_1616_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_val_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1613_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1613_);
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
else
{
lean_object* v_vs_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; size_t v_sz_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
v_vs_1637_ = lean_ctor_get(v_n_1601_, 0);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_b_1602_);
v_sz_1640_ = lean_array_size(v_vs_1637_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_1637_, v_sz_1640_, v___x_1641_, v___x_1639_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1657_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_fst_1647_; 
v_fst_1647_ = lean_ctor_get(v_a_1643_, 0);
if (lean_obj_tag(v_fst_1647_) == 0)
{
lean_object* v_snd_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v_snd_1648_ = lean_ctor_get(v_a_1643_, 1);
lean_inc(v_snd_1648_);
lean_dec(v_a_1643_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_snd_1648_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1649_);
v___x_1651_ = v___x_1645_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
else
{
lean_object* v_val_1653_; lean_object* v___x_1655_; 
lean_inc_ref(v_fst_1647_);
lean_dec(v_a_1643_);
v_val_1653_ = lean_ctor_get(v_fst_1647_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v_fst_1647_, 1);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_val_1653_);
v___x_1655_ = v___x_1645_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_val_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_a_1658_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1642_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1642_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object* v_init_1666_, lean_object* v_as_1667_, size_t v_sz_1668_, size_t v_i_1669_, lean_object* v_b_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_lt(v_i_1669_, v_sz_1668_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_b_1670_);
return v___x_1677_;
}
else
{
lean_object* v_snd_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1712_; 
v_snd_1678_ = lean_ctor_get(v_b_1670_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_b_1670_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v_b_1670_, 0);
lean_dec(v_unused_1713_);
v___x_1680_ = v_b_1670_;
v_isShared_1681_ = v_isSharedCheck_1712_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_snd_1678_);
lean_dec(v_b_1670_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1712_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_a_1682_; lean_object* v___x_1683_; 
v_a_1682_ = lean_array_uget_borrowed(v_as_1667_, v_i_1669_);
lean_inc(v_snd_1678_);
v___x_1683_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1666_, v_a_1682_, v_snd_1678_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1703_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1703_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1703_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
if (lean_obj_tag(v_a_1684_) == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_a_1684_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1688_);
v___x_1690_ = v___x_1680_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_snd_1678_);
v___x_1690_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1692_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1690_);
v___x_1692_ = v___x_1686_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
lean_del_object(v___x_1686_);
lean_dec(v_snd_1678_);
v_a_1695_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v_a_1684_, 1);
v___x_1696_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_a_1695_);
lean_ctor_set(v___x_1680_, 0, v___x_1696_);
v___x_1698_ = v___x_1680_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_a_1695_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
size_t v___x_1699_; size_t v___x_1700_; 
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_add(v_i_1669_, v___x_1699_);
v_i_1669_ = v___x_1700_;
v_b_1670_ = v___x_1698_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_del_object(v___x_1680_);
lean_dec(v_snd_1678_);
v_a_1704_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1683_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1683_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1714_, lean_object* v_as_1715_, lean_object* v_sz_1716_, lean_object* v_i_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
size_t v_sz_boxed_1724_; size_t v_i_boxed_1725_; lean_object* v_res_1726_; 
v_sz_boxed_1724_ = lean_unbox_usize(v_sz_1716_);
lean_dec(v_sz_1716_);
v_i_boxed_1725_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1714_, v_as_1715_, v_sz_boxed_1724_, v_i_boxed_1725_, v_b_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_as_1715_);
lean_dec(v_init_1714_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object* v_init_1727_, lean_object* v_n_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1727_, v_n_1728_, v_b_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v_n_1728_);
lean_dec(v_init_1727_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1736_, size_t v_sz_1737_, size_t v_i_1738_, lean_object* v_b_1739_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_lt(v_i_1738_, v_sz_1737_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_b_1739_);
return v___x_1742_;
}
else
{
lean_object* v_snd_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1761_; 
v_snd_1743_ = lean_ctor_get(v_b_1739_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_b_1739_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_b_1739_, 0);
lean_dec(v_unused_1762_);
v___x_1745_ = v_b_1739_;
v_isShared_1746_ = v_isSharedCheck_1761_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_snd_1743_);
lean_dec(v_b_1739_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1761_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v_a_1749_; lean_object* v_a_1756_; 
v___x_1747_ = lean_box(0);
v_a_1756_ = lean_array_uget_borrowed(v_as_1736_, v_i_1738_);
if (lean_obj_tag(v_a_1756_) == 0)
{
v_a_1749_ = v_snd_1743_;
goto v___jp_1748_;
}
else
{
lean_object* v_val_1757_; uint8_t v___x_1758_; 
v_val_1757_ = lean_ctor_get(v_a_1756_, 0);
v___x_1758_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1757_);
if (v___x_1758_ == 0)
{
v_a_1749_ = v_snd_1743_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = l_Lean_LocalDecl_fvarId(v_val_1757_);
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v_snd_1743_);
v_a_1749_ = v___x_1760_;
goto v___jp_1748_;
}
}
v___jp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_a_1749_);
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1751_ = v___x_1745_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_a_1749_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
size_t v___x_1752_; size_t v___x_1753_; 
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1738_, v___x_1752_);
v_i_1738_ = v___x_1753_;
v_b_1739_ = v___x_1751_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1763_, lean_object* v_sz_1764_, lean_object* v_i_1765_, lean_object* v_b_1766_, lean_object* v___y_1767_){
_start:
{
size_t v_sz_boxed_1768_; size_t v_i_boxed_1769_; lean_object* v_res_1770_; 
v_sz_boxed_1768_ = lean_unbox_usize(v_sz_1764_);
lean_dec(v_sz_1764_);
v_i_boxed_1769_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1763_, v_sz_boxed_1768_, v_i_boxed_1769_, v_b_1766_);
lean_dec_ref(v_as_1763_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(lean_object* v_as_1771_, size_t v_sz_1772_, size_t v_i_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_usize_dec_lt(v_i_1773_, v_sz_1772_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_b_1774_);
return v___x_1781_;
}
else
{
lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1800_; 
v_snd_1782_ = lean_ctor_get(v_b_1774_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_b_1774_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_b_1774_, 0);
lean_dec(v_unused_1801_);
v___x_1784_ = v_b_1774_;
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_dec(v_b_1774_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v_a_1788_; lean_object* v_a_1795_; 
v___x_1786_ = lean_box(0);
v_a_1795_ = lean_array_uget_borrowed(v_as_1771_, v_i_1773_);
if (lean_obj_tag(v_a_1795_) == 0)
{
v_a_1788_ = v_snd_1782_;
goto v___jp_1787_;
}
else
{
lean_object* v_val_1796_; uint8_t v___x_1797_; 
v_val_1796_ = lean_ctor_get(v_a_1795_, 0);
v___x_1797_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1796_);
if (v___x_1797_ == 0)
{
v_a_1788_ = v_snd_1782_;
goto v___jp_1787_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = l_Lean_LocalDecl_fvarId(v_val_1796_);
v___x_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_snd_1782_);
v_a_1788_ = v___x_1799_;
goto v___jp_1787_;
}
}
v___jp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v_a_1788_);
lean_ctor_set(v___x_1784_, 0, v___x_1786_);
v___x_1790_ = v___x_1784_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1788_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
size_t v___x_1791_; size_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = lean_usize_add(v_i_1773_, v___x_1791_);
v___x_1793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1771_, v_sz_1772_, v___x_1792_, v___x_1790_);
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(lean_object* v_as_1802_, lean_object* v_sz_1803_, lean_object* v_i_1804_, lean_object* v_b_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1803_);
lean_dec(v_sz_1803_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_1802_, v_sz_boxed_1811_, v_i_boxed_1812_, v_b_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_as_1802_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(lean_object* v_t_1814_, lean_object* v_init_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_root_1821_; lean_object* v_tail_1822_; lean_object* v___x_1823_; 
v_root_1821_ = lean_ctor_get(v_t_1814_, 0);
v_tail_1822_ = lean_ctor_get(v_t_1814_, 1);
lean_inc(v_init_1815_);
v___x_1823_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1815_, v_root_1821_, v_init_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v_init_1815_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1860_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1860_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1860_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
if (lean_obj_tag(v_a_1824_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; 
v_a_1828_ = lean_ctor_get(v_a_1824_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v_a_1824_, 1);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v_a_1828_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; size_t v_sz_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
lean_del_object(v___x_1826_);
v_a_1832_ = lean_ctor_get(v_a_1824_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v_a_1824_, 1);
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v_a_1832_);
v_sz_1835_ = lean_array_size(v_tail_1822_);
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_1822_, v_sz_1835_, v___x_1836_, v___x_1834_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1851_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1851_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1851_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_fst_1842_; 
v_fst_1842_ = lean_ctor_get(v_a_1838_, 0);
if (lean_obj_tag(v_fst_1842_) == 0)
{
lean_object* v_snd_1843_; lean_object* v___x_1845_; 
v_snd_1843_ = lean_ctor_get(v_a_1838_, 1);
lean_inc(v_snd_1843_);
lean_dec(v_a_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_snd_1843_);
v___x_1845_ = v___x_1840_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_snd_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
else
{
lean_object* v_val_1847_; lean_object* v___x_1849_; 
lean_inc_ref(v_fst_1842_);
lean_dec(v_a_1838_);
v_val_1847_ = lean_ctor_get(v_fst_1842_, 0);
lean_inc(v_val_1847_);
lean_dec_ref_known(v_fst_1842_, 1);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_val_1847_);
v___x_1849_ = v___x_1840_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_val_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1837_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1837_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1823_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1823_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(lean_object* v_t_1869_, lean_object* v_init_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_t_1869_, v_init_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v_t_1869_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_2050_, lean_object* v_x_2051_){
_start:
{
if (lean_obj_tag(v_x_2051_) == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_box(0);
return v___x_2052_;
}
else
{
lean_object* v_key_2053_; lean_object* v_value_2054_; lean_object* v_tail_2055_; uint8_t v___x_2056_; 
v_key_2053_ = lean_ctor_get(v_x_2051_, 0);
v_value_2054_ = lean_ctor_get(v_x_2051_, 1);
v_tail_2055_ = lean_ctor_get(v_x_2051_, 2);
v___x_2056_ = l_Lean_ExprStructEq_beq(v_key_2053_, v_a_2050_);
if (v___x_2056_ == 0)
{
v_x_2051_ = v_tail_2055_;
goto _start;
}
else
{
lean_object* v___x_2058_; 
lean_inc(v_value_2054_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_value_2054_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_2059_, lean_object* v_x_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2059_, v_x_2060_);
lean_dec(v_x_2060_);
lean_dec_ref(v_a_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_buckets_2064_; lean_object* v___x_2065_; uint64_t v___x_2066_; uint64_t v___x_2067_; uint64_t v___x_2068_; uint64_t v_fold_2069_; uint64_t v___x_2070_; uint64_t v___x_2071_; uint64_t v___x_2072_; size_t v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; size_t v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_buckets_2064_ = lean_ctor_get(v_m_2062_, 1);
v___x_2065_ = lean_array_get_size(v_buckets_2064_);
v___x_2066_ = l_Lean_ExprStructEq_hash(v_a_2063_);
v___x_2067_ = 32ULL;
v___x_2068_ = lean_uint64_shift_right(v___x_2066_, v___x_2067_);
v_fold_2069_ = lean_uint64_xor(v___x_2066_, v___x_2068_);
v___x_2070_ = 16ULL;
v___x_2071_ = lean_uint64_shift_right(v_fold_2069_, v___x_2070_);
v___x_2072_ = lean_uint64_xor(v_fold_2069_, v___x_2071_);
v___x_2073_ = lean_uint64_to_usize(v___x_2072_);
v___x_2074_ = lean_usize_of_nat(v___x_2065_);
v___x_2075_ = ((size_t)1ULL);
v___x_2076_ = lean_usize_sub(v___x_2074_, v___x_2075_);
v___x_2077_ = lean_usize_land(v___x_2073_, v___x_2076_);
v___x_2078_ = lean_array_uget_borrowed(v_buckets_2064_, v___x_2077_);
v___x_2079_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2063_, v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2080_, v_a_2081_);
lean_dec_ref(v_a_2081_);
lean_dec_ref(v_m_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_apply_1(v_x_2084_, lean_box(0));
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_x_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_2090_, v_x_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2095_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = l_Lean_interruptExceptionId;
v___x_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___x_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_2103_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = l_Lean_maxRecDepthErrorMessage;
v___x_2110_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_2112_ = l_Lean_MessageData_ofFormat(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_2114_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_2115_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_ref_2116_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object* v_x_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___y_2130_; lean_object* v___y_2140_; uint8_t v___y_2141_; uint8_t v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; uint8_t v___y_2156_; lean_object* v_fileName_2162_; lean_object* v_fileMap_2163_; lean_object* v_options_2164_; lean_object* v_currRecDepth_2165_; lean_object* v_maxRecDepth_2166_; lean_object* v_ref_2167_; lean_object* v_currNamespace_2168_; lean_object* v_openDecls_2169_; lean_object* v_initHeartbeats_2170_; lean_object* v_maxHeartbeats_2171_; lean_object* v_quotContext_2172_; lean_object* v_currMacroScope_2173_; uint8_t v_diag_2174_; lean_object* v_cancelTk_x3f_2175_; uint8_t v_suppressElabErrors_2176_; lean_object* v_inheritedTraceOptions_2177_; 
v_fileName_2162_ = lean_ctor_get(v___y_2126_, 0);
v_fileMap_2163_ = lean_ctor_get(v___y_2126_, 1);
v_options_2164_ = lean_ctor_get(v___y_2126_, 2);
v_currRecDepth_2165_ = lean_ctor_get(v___y_2126_, 3);
v_maxRecDepth_2166_ = lean_ctor_get(v___y_2126_, 4);
v_ref_2167_ = lean_ctor_get(v___y_2126_, 5);
v_currNamespace_2168_ = lean_ctor_get(v___y_2126_, 6);
v_openDecls_2169_ = lean_ctor_get(v___y_2126_, 7);
v_initHeartbeats_2170_ = lean_ctor_get(v___y_2126_, 8);
v_maxHeartbeats_2171_ = lean_ctor_get(v___y_2126_, 9);
v_quotContext_2172_ = lean_ctor_get(v___y_2126_, 10);
v_currMacroScope_2173_ = lean_ctor_get(v___y_2126_, 11);
v_diag_2174_ = lean_ctor_get_uint8(v___y_2126_, sizeof(void*)*14);
v_cancelTk_x3f_2175_ = lean_ctor_get(v___y_2126_, 12);
v_suppressElabErrors_2176_ = lean_ctor_get_uint8(v___y_2126_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2177_ = lean_ctor_get(v___y_2126_, 13);
if (lean_obj_tag(v_cancelTk_x3f_2175_) == 1)
{
lean_object* v_val_2183_; uint8_t v___x_2184_; 
v_val_2183_ = lean_ctor_get(v_cancelTk_x3f_2175_, 0);
v___x_2184_ = l_IO_CancelToken_isSet(v_val_2183_);
if (v___x_2184_ == 0)
{
goto v___jp_2178_;
}
else
{
lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_x_2124_);
v___x_2185_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
goto v___jp_2178_;
}
v___jp_2129_:
{
if (lean_obj_tag(v___y_2130_) == 0)
{
return v___y_2130_;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
v_a_2131_ = lean_ctor_get(v___y_2130_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___y_2130_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___y_2130_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___y_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
v___jp_2139_:
{
if (v___y_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_nat_add(v___y_2143_, v___x_2157_);
lean_inc_ref(v___y_2151_);
lean_inc(v___y_2146_);
lean_inc(v___y_2145_);
lean_inc(v___y_2144_);
lean_inc(v___y_2149_);
lean_inc(v___y_2148_);
lean_inc(v___y_2155_);
lean_inc(v___y_2150_);
lean_inc(v___y_2147_);
lean_inc(v___y_2152_);
lean_inc_ref(v___y_2154_);
lean_inc_ref(v___y_2140_);
lean_inc_ref(v___y_2153_);
v___x_2159_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2159_, 0, v___y_2153_);
lean_ctor_set(v___x_2159_, 1, v___y_2140_);
lean_ctor_set(v___x_2159_, 2, v___y_2154_);
lean_ctor_set(v___x_2159_, 3, v___x_2158_);
lean_ctor_set(v___x_2159_, 4, v___y_2152_);
lean_ctor_set(v___x_2159_, 5, v___y_2147_);
lean_ctor_set(v___x_2159_, 6, v___y_2150_);
lean_ctor_set(v___x_2159_, 7, v___y_2155_);
lean_ctor_set(v___x_2159_, 8, v___y_2148_);
lean_ctor_set(v___x_2159_, 9, v___y_2149_);
lean_ctor_set(v___x_2159_, 10, v___y_2144_);
lean_ctor_set(v___x_2159_, 11, v___y_2145_);
lean_ctor_set(v___x_2159_, 12, v___y_2146_);
lean_ctor_set(v___x_2159_, 13, v___y_2151_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*14, v___y_2141_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*14 + 1, v___y_2142_);
lean_inc(v___y_2127_);
lean_inc(v___y_2125_);
v___x_2160_ = lean_apply_4(v_x_2124_, v___y_2125_, v___x_2159_, v___y_2127_, lean_box(0));
v___y_2130_ = v___x_2160_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2161_; 
lean_dec_ref(v_x_2124_);
lean_inc(v___y_2147_);
v___x_2161_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v___y_2147_);
v___y_2130_ = v___x_2161_;
goto v___jp_2129_;
}
}
v___jp_2178_:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; uint8_t v___x_2181_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_nat_dec_eq(v_maxRecDepth_2166_, v___x_2179_);
v___x_2181_ = lean_bool_not(v___x_2180_);
if (v___x_2181_ == 0)
{
v___y_2140_ = v_fileMap_2163_;
v___y_2141_ = v_diag_2174_;
v___y_2142_ = v_suppressElabErrors_2176_;
v___y_2143_ = v_currRecDepth_2165_;
v___y_2144_ = v_quotContext_2172_;
v___y_2145_ = v_currMacroScope_2173_;
v___y_2146_ = v_cancelTk_x3f_2175_;
v___y_2147_ = v_ref_2167_;
v___y_2148_ = v_initHeartbeats_2170_;
v___y_2149_ = v_maxHeartbeats_2171_;
v___y_2150_ = v_currNamespace_2168_;
v___y_2151_ = v_inheritedTraceOptions_2177_;
v___y_2152_ = v_maxRecDepth_2166_;
v___y_2153_ = v_fileName_2162_;
v___y_2154_ = v_options_2164_;
v___y_2155_ = v_openDecls_2169_;
v___y_2156_ = v___x_2181_;
goto v___jp_2139_;
}
else
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_nat_dec_eq(v_currRecDepth_2165_, v_maxRecDepth_2166_);
v___y_2140_ = v_fileMap_2163_;
v___y_2141_ = v_diag_2174_;
v___y_2142_ = v_suppressElabErrors_2176_;
v___y_2143_ = v_currRecDepth_2165_;
v___y_2144_ = v_quotContext_2172_;
v___y_2145_ = v_currMacroScope_2173_;
v___y_2146_ = v_cancelTk_x3f_2175_;
v___y_2147_ = v_ref_2167_;
v___y_2148_ = v_initHeartbeats_2170_;
v___y_2149_ = v_maxHeartbeats_2171_;
v___y_2150_ = v_currNamespace_2168_;
v___y_2151_ = v_inheritedTraceOptions_2177_;
v___y_2152_ = v_maxRecDepth_2166_;
v___y_2153_ = v_fileName_2162_;
v___y_2154_ = v_options_2164_;
v___y_2155_ = v_openDecls_2169_;
v___y_2156_ = v___x_2182_;
goto v___jp_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_2200_, lean_object* v_x_2201_){
_start:
{
if (lean_obj_tag(v_x_2201_) == 0)
{
return v_x_2200_;
}
else
{
lean_object* v_key_2202_; lean_object* v_value_2203_; lean_object* v_tail_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2227_; 
v_key_2202_ = lean_ctor_get(v_x_2201_, 0);
v_value_2203_ = lean_ctor_get(v_x_2201_, 1);
v_tail_2204_ = lean_ctor_get(v_x_2201_, 2);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_x_2201_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2206_ = v_x_2201_;
v_isShared_2207_ = v_isSharedCheck_2227_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_tail_2204_);
lean_inc(v_value_2203_);
lean_inc(v_key_2202_);
lean_dec(v_x_2201_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2227_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v_fold_2212_; uint64_t v___x_2213_; uint64_t v___x_2214_; uint64_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2208_ = lean_array_get_size(v_x_2200_);
v___x_2209_ = l_Lean_ExprStructEq_hash(v_key_2202_);
v___x_2210_ = 32ULL;
v___x_2211_ = lean_uint64_shift_right(v___x_2209_, v___x_2210_);
v_fold_2212_ = lean_uint64_xor(v___x_2209_, v___x_2211_);
v___x_2213_ = 16ULL;
v___x_2214_ = lean_uint64_shift_right(v_fold_2212_, v___x_2213_);
v___x_2215_ = lean_uint64_xor(v_fold_2212_, v___x_2214_);
v___x_2216_ = lean_uint64_to_usize(v___x_2215_);
v___x_2217_ = lean_usize_of_nat(v___x_2208_);
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_sub(v___x_2217_, v___x_2218_);
v___x_2220_ = lean_usize_land(v___x_2216_, v___x_2219_);
v___x_2221_ = lean_array_uget_borrowed(v_x_2200_, v___x_2220_);
lean_inc(v___x_2221_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 2, v___x_2221_);
v___x_2223_ = v___x_2206_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_key_2202_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_value_2203_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_array_uset(v_x_2200_, v___x_2220_, v___x_2223_);
v_x_2200_ = v___x_2224_;
v_x_2201_ = v_tail_2204_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_2228_, lean_object* v_source_2229_, lean_object* v_target_2230_){
_start:
{
lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = lean_array_get_size(v_source_2229_);
v___x_2232_ = lean_nat_dec_lt(v_i_2228_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_dec_ref(v_source_2229_);
lean_dec(v_i_2228_);
return v_target_2230_;
}
else
{
lean_object* v_es_2233_; lean_object* v___x_2234_; lean_object* v_source_2235_; lean_object* v_target_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_es_2233_ = lean_array_fget(v_source_2229_, v_i_2228_);
v___x_2234_ = lean_box(0);
v_source_2235_ = lean_array_fset(v_source_2229_, v_i_2228_, v___x_2234_);
v_target_2236_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_2230_, v_es_2233_);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_i_2228_, v___x_2237_);
lean_dec(v_i_2228_);
v_i_2228_ = v___x_2238_;
v_source_2229_ = v_source_2235_;
v_target_2230_ = v_target_2236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_2240_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_nbuckets_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2241_ = lean_array_get_size(v_data_2240_);
v___x_2242_ = lean_unsigned_to_nat(2u);
v_nbuckets_2243_ = lean_nat_mul(v___x_2241_, v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_mk_array(v_nbuckets_2243_, v___x_2245_);
v___x_2247_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_2244_, v_data_2240_, v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_2248_, lean_object* v_b_2249_, lean_object* v_x_2250_){
_start:
{
if (lean_obj_tag(v_x_2250_) == 0)
{
lean_dec(v_b_2249_);
lean_dec_ref(v_a_2248_);
return v_x_2250_;
}
else
{
lean_object* v_key_2251_; lean_object* v_value_2252_; lean_object* v_tail_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2265_; 
v_key_2251_ = lean_ctor_get(v_x_2250_, 0);
v_value_2252_ = lean_ctor_get(v_x_2250_, 1);
v_tail_2253_ = lean_ctor_get(v_x_2250_, 2);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_x_2250_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2255_ = v_x_2250_;
v_isShared_2256_ = v_isSharedCheck_2265_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_tail_2253_);
lean_inc(v_value_2252_);
lean_inc(v_key_2251_);
lean_dec(v_x_2250_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2265_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
uint8_t v___x_2257_; 
v___x_2257_ = l_Lean_ExprStructEq_beq(v_key_2251_, v_a_2248_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2248_, v_b_2249_, v_tail_2253_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 2, v___x_2258_);
v___x_2260_ = v___x_2255_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_key_2251_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_value_2252_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v___x_2258_);
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
lean_dec(v_value_2252_);
lean_dec(v_key_2251_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 1, v_b_2249_);
lean_ctor_set(v___x_2255_, 0, v_a_2248_);
v___x_2263_ = v___x_2255_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2248_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_b_2249_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_tail_2253_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_2266_, lean_object* v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2267_) == 0)
{
uint8_t v___x_2268_; 
v___x_2268_ = 0;
return v___x_2268_;
}
else
{
lean_object* v_key_2269_; lean_object* v_tail_2270_; uint8_t v___x_2271_; 
v_key_2269_ = lean_ctor_get(v_x_2267_, 0);
v_tail_2270_ = lean_ctor_get(v_x_2267_, 2);
v___x_2271_ = l_Lean_ExprStructEq_beq(v_key_2269_, v_a_2266_);
if (v___x_2271_ == 0)
{
v_x_2267_ = v_tail_2270_;
goto _start;
}
else
{
return v___x_2271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_2273_, lean_object* v_x_2274_){
_start:
{
uint8_t v_res_2275_; lean_object* v_r_2276_; 
v_res_2275_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2273_, v_x_2274_);
lean_dec(v_x_2274_);
lean_dec_ref(v_a_2273_);
v_r_2276_ = lean_box(v_res_2275_);
return v_r_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object* v_m_2277_, lean_object* v_a_2278_, lean_object* v_b_2279_){
_start:
{
lean_object* v_size_2280_; lean_object* v_buckets_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2324_; 
v_size_2280_ = lean_ctor_get(v_m_2277_, 0);
v_buckets_2281_ = lean_ctor_get(v_m_2277_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_m_2277_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2283_ = v_m_2277_;
v_isShared_2284_ = v_isSharedCheck_2324_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_buckets_2281_);
lean_inc(v_size_2280_);
lean_dec(v_m_2277_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2324_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; uint64_t v___x_2286_; uint64_t v___x_2287_; uint64_t v___x_2288_; uint64_t v_fold_2289_; uint64_t v___x_2290_; uint64_t v___x_2291_; uint64_t v___x_2292_; size_t v___x_2293_; size_t v___x_2294_; size_t v___x_2295_; size_t v___x_2296_; size_t v___x_2297_; lean_object* v_bkt_2298_; uint8_t v___x_2299_; 
v___x_2285_ = lean_array_get_size(v_buckets_2281_);
v___x_2286_ = l_Lean_ExprStructEq_hash(v_a_2278_);
v___x_2287_ = 32ULL;
v___x_2288_ = lean_uint64_shift_right(v___x_2286_, v___x_2287_);
v_fold_2289_ = lean_uint64_xor(v___x_2286_, v___x_2288_);
v___x_2290_ = 16ULL;
v___x_2291_ = lean_uint64_shift_right(v_fold_2289_, v___x_2290_);
v___x_2292_ = lean_uint64_xor(v_fold_2289_, v___x_2291_);
v___x_2293_ = lean_uint64_to_usize(v___x_2292_);
v___x_2294_ = lean_usize_of_nat(v___x_2285_);
v___x_2295_ = ((size_t)1ULL);
v___x_2296_ = lean_usize_sub(v___x_2294_, v___x_2295_);
v___x_2297_ = lean_usize_land(v___x_2293_, v___x_2296_);
v_bkt_2298_ = lean_array_uget_borrowed(v_buckets_2281_, v___x_2297_);
v___x_2299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2278_, v_bkt_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v_size_x27_2301_; lean_object* v___x_2302_; lean_object* v_buckets_x27_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2300_ = lean_unsigned_to_nat(1u);
v_size_x27_2301_ = lean_nat_add(v_size_2280_, v___x_2300_);
lean_dec(v_size_2280_);
lean_inc(v_bkt_2298_);
v___x_2302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2302_, 0, v_a_2278_);
lean_ctor_set(v___x_2302_, 1, v_b_2279_);
lean_ctor_set(v___x_2302_, 2, v_bkt_2298_);
v_buckets_x27_2303_ = lean_array_uset(v_buckets_2281_, v___x_2297_, v___x_2302_);
v___x_2304_ = lean_unsigned_to_nat(4u);
v___x_2305_ = lean_nat_mul(v_size_x27_2301_, v___x_2304_);
v___x_2306_ = lean_unsigned_to_nat(3u);
v___x_2307_ = lean_nat_div(v___x_2305_, v___x_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_array_get_size(v_buckets_x27_2303_);
v___x_2309_ = lean_nat_dec_le(v___x_2307_, v___x_2308_);
lean_dec(v___x_2307_);
if (v___x_2309_ == 0)
{
lean_object* v_val_2310_; lean_object* v___x_2312_; 
v_val_2310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_2303_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v_val_2310_);
lean_ctor_set(v___x_2283_, 0, v_size_x27_2301_);
v___x_2312_ = v___x_2283_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_size_x27_2301_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_val_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
else
{
lean_object* v___x_2315_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v_buckets_x27_2303_);
lean_ctor_set(v___x_2283_, 0, v_size_x27_2301_);
v___x_2315_ = v___x_2283_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_size_x27_2301_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_buckets_x27_2303_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v___x_2317_; lean_object* v_buckets_x27_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
lean_inc(v_bkt_2298_);
v___x_2317_ = lean_box(0);
v_buckets_x27_2318_ = lean_array_uset(v_buckets_2281_, v___x_2297_, v___x_2317_);
v___x_2319_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2278_, v_b_2279_, v_bkt_2298_);
v___x_2320_ = lean_array_uset(v_buckets_x27_2318_, v___x_2297_, v___x_2319_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v___x_2320_);
v___x_2322_ = v___x_2283_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_size_2280_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object* v_a_2325_, lean_object* v_e_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_st_ref_take(v_a_2325_);
v___x_2330_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2329_, v_e_2326_, v_a_2327_);
v___x_2331_ = lean_st_ref_set(v_a_2325_, v___x_2330_);
v___x_2332_ = lean_box(0);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2333_, lean_object* v_e_2334_, lean_object* v_a_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2333_, v_e_2334_, v_a_2335_);
lean_dec(v_a_2333_);
return v_res_2337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2339_; lean_object* v_dummy_2340_; 
v___x_2339_ = lean_box(0);
v_dummy_2340_ = l_Lean_Expr_sort___override(v___x_2339_);
return v_dummy_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object* v_pre_2341_, lean_object* v_post_2342_, size_t v_sz_2343_, size_t v_i_2344_, lean_object* v_bs_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
uint8_t v___x_2350_; 
v___x_2350_ = lean_usize_dec_lt(v_i_2344_, v_sz_2343_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2341_);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_bs_2345_);
return v___x_2351_;
}
else
{
lean_object* v_v_2352_; lean_object* v___x_2353_; 
v_v_2352_ = lean_array_uget_borrowed(v_bs_2345_, v_i_2344_);
lean_inc(v_v_2352_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2341_);
v___x_2353_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2341_, v_post_2342_, v_v_2352_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; lean_object* v_bs_x27_2356_; size_t v___x_2357_; size_t v___x_2358_; lean_object* v___x_2359_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = lean_unsigned_to_nat(0u);
v_bs_x27_2356_ = lean_array_uset(v_bs_2345_, v_i_2344_, v___x_2355_);
v___x_2357_ = ((size_t)1ULL);
v___x_2358_ = lean_usize_add(v_i_2344_, v___x_2357_);
v___x_2359_ = lean_array_uset(v_bs_x27_2356_, v_i_2344_, v_a_2354_);
v_i_2344_ = v___x_2358_;
v_bs_2345_ = v___x_2359_;
goto _start;
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v_bs_2345_);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2341_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object* v_pre_2369_, lean_object* v_post_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
if (lean_obj_tag(v_x_2371_) == 5)
{
lean_object* v_fn_2378_; lean_object* v_arg_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_fn_2378_ = lean_ctor_get(v_x_2371_, 0);
lean_inc_ref(v_fn_2378_);
v_arg_2379_ = lean_ctor_get(v_x_2371_, 1);
lean_inc_ref(v_arg_2379_);
lean_dec_ref_known(v_x_2371_, 2);
v___x_2380_ = lean_array_set(v_x_2372_, v_x_2373_, v_arg_2379_);
v___x_2381_ = lean_unsigned_to_nat(1u);
v___x_2382_ = lean_nat_sub(v_x_2373_, v___x_2381_);
lean_dec(v_x_2373_);
v_x_2371_ = v_fn_2378_;
v_x_2372_ = v___x_2380_;
v_x_2373_ = v___x_2382_;
goto _start;
}
else
{
lean_object* v___x_2384_; 
lean_dec(v_x_2373_);
lean_inc_ref(v_post_2370_);
lean_inc_ref(v_pre_2369_);
v___x_2384_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2369_, v_post_2370_, v_x_2371_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; size_t v_sz_2386_; size_t v___x_2387_; lean_object* v___x_2388_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v_sz_2386_ = lean_array_size(v_x_2372_);
v___x_2387_ = ((size_t)0ULL);
lean_inc_ref(v_post_2370_);
lean_inc_ref(v_pre_2369_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2369_, v_post_2370_, v_sz_2386_, v___x_2387_, v_x_2372_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = l_Lean_mkAppN(v_a_2385_, v_a_2389_);
lean_dec(v_a_2389_);
v___x_2391_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2369_, v_post_2370_, v___x_2390_, v___y_2374_, v___y_2375_, v___y_2376_);
return v___x_2391_;
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_a_2385_);
lean_dec_ref(v_post_2370_);
lean_dec_ref(v_pre_2369_);
v_a_2392_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2388_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2388_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_dec_ref(v_x_2372_);
lean_dec_ref(v_post_2370_);
lean_dec_ref(v_pre_2369_);
return v___x_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object* v___x_2400_, lean_object* v_pre_2401_, lean_object* v_e_2402_, lean_object* v_post_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___y_2409_; uint8_t v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; uint8_t v___y_2416_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; uint8_t v___y_2429_; lean_object* v___y_2430_; uint8_t v___y_2431_; lean_object* v___y_2439_; uint8_t v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; uint8_t v___y_2444_; lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Core_checkSystem(v___x_2400_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v___x_2452_; 
lean_dec_ref_known(v___x_2451_, 1);
lean_inc_ref(v_pre_2401_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
lean_inc_ref(v_e_2402_);
v___x_2452_ = lean_apply_4(v_pre_2401_, v_e_2402_, v___y_2405_, v___y_2406_, lean_box(0));
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2542_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2542_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2542_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___y_2458_; 
switch(lean_obj_tag(v_a_2453_))
{
case 0:
{
lean_object* v_e_2532_; lean_object* v___x_2534_; 
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_e_2402_);
lean_dec_ref(v_pre_2401_);
v_e_2532_ = lean_ctor_get(v_a_2453_, 0);
lean_inc_ref(v_e_2532_);
lean_dec_ref_known(v_a_2453_, 1);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_e_2532_);
v___x_2534_ = v___x_2455_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_e_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
case 1:
{
lean_object* v_e_2536_; lean_object* v___x_2537_; 
lean_del_object(v___x_2455_);
lean_dec_ref(v_e_2402_);
v_e_2536_ = lean_ctor_get(v_a_2453_, 0);
lean_inc_ref(v_e_2536_);
lean_dec_ref_known(v_a_2453_, 1);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_e_2536_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v___x_2539_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v_a_2538_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2539_;
}
else
{
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2537_;
}
}
default: 
{
lean_object* v_e_x3f_2540_; 
lean_del_object(v___x_2455_);
v_e_x3f_2540_ = lean_ctor_get(v_a_2453_, 0);
lean_inc(v_e_x3f_2540_);
lean_dec_ref_known(v_a_2453_, 1);
if (lean_obj_tag(v_e_x3f_2540_) == 0)
{
v___y_2458_ = v_e_2402_;
goto v___jp_2457_;
}
else
{
lean_object* v_val_2541_; 
lean_dec_ref(v_e_2402_);
v_val_2541_ = lean_ctor_get(v_e_x3f_2540_, 0);
lean_inc(v_val_2541_);
lean_dec_ref_known(v_e_x3f_2540_, 1);
v___y_2458_ = v_val_2541_;
goto v___jp_2457_;
}
}
}
v___jp_2457_:
{
switch(lean_obj_tag(v___y_2458_))
{
case 7:
{
lean_object* v_binderName_2459_; lean_object* v_binderType_2460_; lean_object* v_body_2461_; uint8_t v_binderInfo_2462_; lean_object* v___x_2463_; 
v_binderName_2459_ = lean_ctor_get(v___y_2458_, 0);
lean_inc(v_binderName_2459_);
v_binderType_2460_ = lean_ctor_get(v___y_2458_, 1);
v_body_2461_ = lean_ctor_get(v___y_2458_, 2);
v_binderInfo_2462_ = lean_ctor_get_uint8(v___y_2458_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2460_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_binderType_2460_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
lean_inc_ref(v_body_2461_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_body_2461_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; size_t v___x_2467_; size_t v___x_2468_; uint8_t v___x_2469_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_ptr_addr(v_binderType_2460_);
v___x_2468_ = lean_ptr_addr(v_a_2464_);
v___x_2469_ = lean_usize_dec_eq(v___x_2467_, v___x_2468_);
if (v___x_2469_ == 0)
{
v___y_2439_ = v_a_2466_;
v___y_2440_ = v_binderInfo_2462_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v_binderName_2459_;
v___y_2443_ = v_a_2464_;
v___y_2444_ = v___x_2469_;
goto v___jp_2438_;
}
else
{
size_t v___x_2470_; size_t v___x_2471_; uint8_t v___x_2472_; 
v___x_2470_ = lean_ptr_addr(v_body_2461_);
v___x_2471_ = lean_ptr_addr(v_a_2466_);
v___x_2472_ = lean_usize_dec_eq(v___x_2470_, v___x_2471_);
v___y_2439_ = v_a_2466_;
v___y_2440_ = v_binderInfo_2462_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v_binderName_2459_;
v___y_2443_ = v_a_2464_;
v___y_2444_ = v___x_2472_;
goto v___jp_2438_;
}
}
else
{
lean_dec(v_a_2464_);
lean_dec(v_binderName_2459_);
lean_dec_ref_known(v___y_2458_, 3);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2465_;
}
}
else
{
lean_dec(v_binderName_2459_);
lean_dec_ref_known(v___y_2458_, 3);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2463_;
}
}
case 6:
{
lean_object* v_binderName_2473_; lean_object* v_binderType_2474_; lean_object* v_body_2475_; uint8_t v_binderInfo_2476_; lean_object* v___x_2477_; 
v_binderName_2473_ = lean_ctor_get(v___y_2458_, 0);
lean_inc(v_binderName_2473_);
v_binderType_2474_ = lean_ctor_get(v___y_2458_, 1);
v_body_2475_ = lean_ctor_get(v___y_2458_, 2);
v_binderInfo_2476_ = lean_ctor_get_uint8(v___y_2458_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2474_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_binderType_2474_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
lean_inc_ref(v_body_2475_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_body_2475_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; size_t v___x_2481_; size_t v___x_2482_; uint8_t v___x_2483_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2481_ = lean_ptr_addr(v_binderType_2474_);
v___x_2482_ = lean_ptr_addr(v_a_2478_);
v___x_2483_ = lean_usize_dec_eq(v___x_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
v___y_2426_ = v___y_2458_;
v___y_2427_ = v_a_2480_;
v___y_2428_ = v_binderName_2473_;
v___y_2429_ = v_binderInfo_2476_;
v___y_2430_ = v_a_2478_;
v___y_2431_ = v___x_2483_;
goto v___jp_2425_;
}
else
{
size_t v___x_2484_; size_t v___x_2485_; uint8_t v___x_2486_; 
v___x_2484_ = lean_ptr_addr(v_body_2475_);
v___x_2485_ = lean_ptr_addr(v_a_2480_);
v___x_2486_ = lean_usize_dec_eq(v___x_2484_, v___x_2485_);
v___y_2426_ = v___y_2458_;
v___y_2427_ = v_a_2480_;
v___y_2428_ = v_binderName_2473_;
v___y_2429_ = v_binderInfo_2476_;
v___y_2430_ = v_a_2478_;
v___y_2431_ = v___x_2486_;
goto v___jp_2425_;
}
}
else
{
lean_dec(v_a_2478_);
lean_dec_ref_known(v___y_2458_, 3);
lean_dec(v_binderName_2473_);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2479_;
}
}
else
{
lean_dec(v_binderName_2473_);
lean_dec_ref_known(v___y_2458_, 3);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2477_;
}
}
case 8:
{
lean_object* v_declName_2487_; lean_object* v_type_2488_; lean_object* v_value_2489_; lean_object* v_body_2490_; uint8_t v_nondep_2491_; lean_object* v___x_2492_; 
v_declName_2487_ = lean_ctor_get(v___y_2458_, 0);
lean_inc(v_declName_2487_);
v_type_2488_ = lean_ctor_get(v___y_2458_, 1);
v_value_2489_ = lean_ctor_get(v___y_2458_, 2);
v_body_2490_ = lean_ctor_get(v___y_2458_, 3);
lean_inc_ref(v_body_2490_);
v_nondep_2491_ = lean_ctor_get_uint8(v___y_2458_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2488_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_type_2488_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
lean_inc_ref(v_value_2489_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2494_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_value_2489_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
lean_inc_ref(v_body_2490_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_body_2490_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; size_t v___x_2498_; size_t v___x_2499_; uint8_t v___x_2500_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v___x_2498_ = lean_ptr_addr(v_type_2488_);
v___x_2499_ = lean_ptr_addr(v_a_2493_);
v___x_2500_ = lean_usize_dec_eq(v___x_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
v___y_2409_ = v_body_2490_;
v___y_2410_ = v_nondep_2491_;
v___y_2411_ = v_a_2495_;
v___y_2412_ = v___y_2458_;
v___y_2413_ = v_a_2497_;
v___y_2414_ = v_declName_2487_;
v___y_2415_ = v_a_2493_;
v___y_2416_ = v___x_2500_;
goto v___jp_2408_;
}
else
{
size_t v___x_2501_; size_t v___x_2502_; uint8_t v___x_2503_; 
v___x_2501_ = lean_ptr_addr(v_value_2489_);
v___x_2502_ = lean_ptr_addr(v_a_2495_);
v___x_2503_ = lean_usize_dec_eq(v___x_2501_, v___x_2502_);
v___y_2409_ = v_body_2490_;
v___y_2410_ = v_nondep_2491_;
v___y_2411_ = v_a_2495_;
v___y_2412_ = v___y_2458_;
v___y_2413_ = v_a_2497_;
v___y_2414_ = v_declName_2487_;
v___y_2415_ = v_a_2493_;
v___y_2416_ = v___x_2503_;
goto v___jp_2408_;
}
}
else
{
lean_dec(v_a_2495_);
lean_dec(v_a_2493_);
lean_dec_ref(v_body_2490_);
lean_dec_ref_known(v___y_2458_, 4);
lean_dec(v_declName_2487_);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2496_;
}
}
else
{
lean_dec(v_a_2493_);
lean_dec_ref(v_body_2490_);
lean_dec_ref_known(v___y_2458_, 4);
lean_dec(v_declName_2487_);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2494_;
}
}
else
{
lean_dec_ref(v_body_2490_);
lean_dec(v_declName_2487_);
lean_dec_ref_known(v___y_2458_, 4);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2492_;
}
}
case 5:
{
lean_object* v_dummy_2504_; lean_object* v_nargs_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_dummy_2504_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_2505_ = l_Lean_Expr_getAppNumArgs(v___y_2458_);
lean_inc(v_nargs_2505_);
v___x_2506_ = lean_mk_array(v_nargs_2505_, v_dummy_2504_);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_nat_sub(v_nargs_2505_, v___x_2507_);
lean_dec(v_nargs_2505_);
v___x_2509_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2401_, v_post_2403_, v___y_2458_, v___x_2506_, v___x_2508_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2509_;
}
case 10:
{
lean_object* v_data_2510_; lean_object* v_expr_2511_; lean_object* v___x_2512_; 
v_data_2510_ = lean_ctor_get(v___y_2458_, 0);
v_expr_2511_ = lean_ctor_get(v___y_2458_, 1);
lean_inc_ref(v_expr_2511_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_expr_2511_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; size_t v___x_2514_; size_t v___x_2515_; uint8_t v___x_2516_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = lean_ptr_addr(v_expr_2511_);
v___x_2515_ = lean_ptr_addr(v_a_2513_);
v___x_2516_ = lean_usize_dec_eq(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_inc(v_data_2510_);
lean_dec_ref_known(v___y_2458_, 2);
v___x_2517_ = l_Lean_Expr_mdata___override(v_data_2510_, v_a_2513_);
v___x_2518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2517_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2518_;
}
else
{
lean_object* v___x_2519_; 
lean_dec(v_a_2513_);
v___x_2519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___y_2458_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2519_;
}
}
else
{
lean_dec_ref_known(v___y_2458_, 2);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2512_;
}
}
case 11:
{
lean_object* v_typeName_2520_; lean_object* v_idx_2521_; lean_object* v_struct_2522_; lean_object* v___x_2523_; 
v_typeName_2520_ = lean_ctor_get(v___y_2458_, 0);
v_idx_2521_ = lean_ctor_get(v___y_2458_, 1);
v_struct_2522_ = lean_ctor_get(v___y_2458_, 2);
lean_inc_ref(v_struct_2522_);
lean_inc_ref(v_post_2403_);
lean_inc_ref(v_pre_2401_);
v___x_2523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2401_, v_post_2403_, v_struct_2522_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; size_t v___x_2525_; size_t v___x_2526_; uint8_t v___x_2527_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2525_ = lean_ptr_addr(v_struct_2522_);
v___x_2526_ = lean_ptr_addr(v_a_2524_);
v___x_2527_ = lean_usize_dec_eq(v___x_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_inc(v_idx_2521_);
lean_inc(v_typeName_2520_);
lean_dec_ref_known(v___y_2458_, 3);
v___x_2528_ = l_Lean_Expr_proj___override(v_typeName_2520_, v_idx_2521_, v_a_2524_);
v___x_2529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2528_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2529_;
}
else
{
lean_object* v___x_2530_; 
lean_dec(v_a_2524_);
v___x_2530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___y_2458_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2530_;
}
}
else
{
lean_dec_ref_known(v___y_2458_, 3);
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_pre_2401_);
return v___x_2523_;
}
}
default: 
{
lean_object* v___x_2531_; 
v___x_2531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___y_2458_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2531_;
}
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_e_2402_);
lean_dec_ref(v_pre_2401_);
v_a_2543_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2452_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2452_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_post_2403_);
lean_dec_ref(v_e_2402_);
lean_dec_ref(v_pre_2401_);
v_a_2551_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2451_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2451_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
v___jp_2408_:
{
if (v___y_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v___y_2412_);
lean_dec_ref(v___y_2409_);
v___x_2417_ = l_Lean_Expr_letE___override(v___y_2414_, v___y_2415_, v___y_2411_, v___y_2413_, v___y_2410_);
v___x_2418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2417_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2418_;
}
else
{
size_t v___x_2419_; size_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2419_ = lean_ptr_addr(v___y_2409_);
lean_dec_ref(v___y_2409_);
v___x_2420_ = lean_ptr_addr(v___y_2413_);
v___x_2421_ = lean_usize_dec_eq(v___x_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref(v___y_2412_);
v___x_2422_ = l_Lean_Expr_letE___override(v___y_2414_, v___y_2415_, v___y_2411_, v___y_2413_, v___y_2410_);
v___x_2423_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2422_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; 
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec_ref(v___y_2411_);
v___x_2424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___y_2412_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2424_;
}
}
}
v___jp_2425_:
{
if (v___y_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec_ref(v___y_2426_);
v___x_2432_ = l_Lean_Expr_lam___override(v___y_2428_, v___y_2430_, v___y_2427_, v___y_2429_);
v___x_2433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2432_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2433_;
}
else
{
uint8_t v___x_2434_; 
v___x_2434_ = l_Lean_instBEqBinderInfo_beq(v___y_2429_, v___y_2429_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref(v___y_2426_);
v___x_2435_ = l_Lean_Expr_lam___override(v___y_2428_, v___y_2430_, v___y_2427_, v___y_2429_);
v___x_2436_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2435_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2436_;
}
else
{
lean_object* v___x_2437_; 
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
v___x_2437_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___y_2426_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2437_;
}
}
}
v___jp_2438_:
{
if (v___y_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_dec_ref(v___y_2441_);
v___x_2445_ = l_Lean_Expr_forallE___override(v___y_2442_, v___y_2443_, v___y_2439_, v___y_2440_);
v___x_2446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2445_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2446_;
}
else
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Lean_instBEqBinderInfo_beq(v___y_2440_, v___y_2440_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec_ref(v___y_2441_);
v___x_2448_ = l_Lean_Expr_forallE___override(v___y_2442_, v___y_2443_, v___y_2439_, v___y_2440_);
v___x_2449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___x_2448_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2449_;
}
else
{
lean_object* v___x_2450_; 
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2439_);
v___x_2450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2401_, v_post_2403_, v___y_2441_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2559_, lean_object* v_pre_2560_, lean_object* v_e_2561_, lean_object* v_post_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_2559_, v_pre_2560_, v_e_2561_, v_post_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object* v_pre_2568_, lean_object* v_post_2569_, lean_object* v_e_2570_, lean_object* v_a_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_inc(v_a_2571_);
v___x_2575_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2575_, 0, lean_box(0));
lean_closure_set(v___x_2575_, 1, lean_box(0));
lean_closure_set(v___x_2575_, 2, v_a_2571_);
v___x_2576_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___x_2575_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2608_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2608_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2608_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_2577_, v_e_2570_);
lean_dec(v_a_2577_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; 
lean_del_object(v___x_2579_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_2570_);
v___f_2583_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2583_, 0, v___x_2582_);
lean_closure_set(v___f_2583_, 1, v_pre_2568_);
lean_closure_set(v___f_2583_, 2, v_e_2570_);
lean_closure_set(v___f_2583_, 3, v_post_2569_);
v___x_2584_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2583_, v_a_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc_n(v_a_2585_, 2);
lean_dec_ref_known(v___x_2584_, 1);
lean_inc(v_a_2571_);
v___f_2586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2586_, 0, v_a_2571_);
lean_closure_set(v___f_2586_, 1, v_e_2570_);
lean_closure_set(v___f_2586_, 2, v_a_2585_);
v___x_2587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___f_2586_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2587_, 0);
lean_dec(v_unused_2595_);
v___x_2589_ = v___x_2587_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_dec(v___x_2587_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_a_2585_);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2585_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_a_2585_);
v_a_2596_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2587_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2587_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_dec_ref(v_e_2570_);
return v___x_2584_;
}
}
else
{
lean_object* v_val_2604_; lean_object* v___x_2606_; 
lean_dec_ref(v_e_2570_);
lean_dec_ref(v_post_2569_);
lean_dec_ref(v_pre_2568_);
v_val_2604_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_val_2604_);
lean_dec_ref_known(v___x_2581_, 1);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v_val_2604_);
v___x_2606_ = v___x_2579_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_val_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v_e_2570_);
lean_dec_ref(v_post_2569_);
lean_dec_ref(v_pre_2568_);
v_a_2609_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2576_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2576_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object* v_pre_2617_, lean_object* v_post_2618_, lean_object* v_e_2619_, lean_object* v_a_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
lean_inc_ref(v_post_2618_);
lean_inc(v___y_2622_);
lean_inc_ref(v___y_2621_);
lean_inc_ref(v_e_2619_);
v___x_2624_ = lean_apply_4(v_post_2618_, v_e_2619_, v___y_2621_, v___y_2622_, lean_box(0));
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2643_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2643_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2643_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
switch(lean_obj_tag(v_a_2625_))
{
case 0:
{
lean_object* v_e_2629_; lean_object* v___x_2631_; 
lean_dec_ref(v_e_2619_);
lean_dec_ref(v_post_2618_);
lean_dec_ref(v_pre_2617_);
v_e_2629_ = lean_ctor_get(v_a_2625_, 0);
lean_inc_ref(v_e_2629_);
lean_dec_ref_known(v_a_2625_, 1);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v_e_2629_);
v___x_2631_ = v___x_2627_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_e_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
case 1:
{
lean_object* v_e_2633_; lean_object* v___x_2634_; 
lean_del_object(v___x_2627_);
lean_dec_ref(v_e_2619_);
v_e_2633_ = lean_ctor_get(v_a_2625_, 0);
lean_inc_ref(v_e_2633_);
lean_dec_ref_known(v_a_2625_, 1);
v___x_2634_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2617_, v_post_2618_, v_e_2633_, v_a_2620_, v___y_2621_, v___y_2622_);
return v___x_2634_;
}
default: 
{
lean_object* v_e_x3f_2635_; 
lean_dec_ref(v_post_2618_);
lean_dec_ref(v_pre_2617_);
v_e_x3f_2635_ = lean_ctor_get(v_a_2625_, 0);
lean_inc(v_e_x3f_2635_);
lean_dec_ref_known(v_a_2625_, 1);
if (lean_obj_tag(v_e_x3f_2635_) == 0)
{
lean_object* v___x_2637_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v_e_2619_);
v___x_2637_ = v___x_2627_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_e_2619_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
else
{
lean_object* v_val_2639_; lean_object* v___x_2641_; 
lean_dec_ref(v_e_2619_);
v_val_2639_ = lean_ctor_get(v_e_x3f_2635_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v_e_x3f_2635_, 1);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v_val_2639_);
v___x_2641_ = v___x_2627_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_val_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_e_2619_);
lean_dec_ref(v_post_2618_);
lean_dec_ref(v_pre_2617_);
v_a_2644_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2624_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2624_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2652_, lean_object* v_post_2653_, lean_object* v_e_2654_, lean_object* v_a_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2652_, v_post_2653_, v_e_2654_, v_a_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v_a_2655_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2660_, lean_object* v_post_2661_, lean_object* v_sz_2662_, lean_object* v_i_2663_, lean_object* v_bs_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
size_t v_sz_boxed_2669_; size_t v_i_boxed_2670_; lean_object* v_res_2671_; 
v_sz_boxed_2669_ = lean_unbox_usize(v_sz_2662_);
lean_dec(v_sz_2662_);
v_i_boxed_2670_ = lean_unbox_usize(v_i_2663_);
lean_dec(v_i_2663_);
v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2660_, v_post_2661_, v_sz_boxed_2669_, v_i_boxed_2670_, v_bs_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_2672_, lean_object* v_post_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2672_, v_post_2673_, v_x_2674_, v_x_2675_, v_x_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(lean_object* v_pre_2682_, lean_object* v_post_2683_, lean_object* v_e_2684_, lean_object* v_a_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2682_, v_post_2683_, v_e_2684_, v_a_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v_a_2685_);
return v_res_2689_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_unsigned_to_nat(16u);
v___x_2692_ = lean_mk_array(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v___x_2693_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
v___x_2697_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2697_, 0, lean_box(0));
lean_closure_set(v___x_2697_, 1, lean_box(0));
lean_closure_set(v___x_2697_, 2, v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object* v_input_2698_, lean_object* v_pre_2699_, lean_object* v_post_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v_a_2706_; lean_object* v___x_2707_; 
v___x_2704_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_2705_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2704_, v___y_2701_, v___y_2702_);
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref(v___x_2705_);
v___x_2707_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2699_, v_post_2700_, v_input_2698_, v_a_2706_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v___x_2709_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2709_, 0, lean_box(0));
lean_closure_set(v___x_2709_, 1, lean_box(0));
lean_closure_set(v___x_2709_, 2, v_a_2706_);
v___x_2710_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2709_, v___y_2701_, v___y_2702_);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; 
v_unused_2718_ = lean_ctor_get(v___x_2710_, 0);
lean_dec(v_unused_2718_);
v___x_2712_ = v___x_2710_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_dec(v___x_2710_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_a_2708_);
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2708_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
lean_dec(v_a_2706_);
return v___x_2707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object* v_input_2719_, lean_object* v_pre_2720_, lean_object* v_post_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2719_, v_pre_2720_, v_post_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* v_e_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v___f_2733_; lean_object* v___x_2734_; 
v___f_2733_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0));
v___x_2734_ = lean_find_expr(v___f_2733_, v_e_2729_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_e_2729_);
return v___x_2735_;
}
else
{
lean_object* v_pre_2736_; lean_object* v___f_2737_; lean_object* v___x_2738_; 
lean_dec_ref_known(v___x_2734_, 1);
v_pre_2736_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1));
v___f_2737_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2));
v___x_2738_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_e_2729_, v_pre_2736_, v___f_2737_, v_a_2730_, v_a_2731_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object* v_e_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2739_, v_a_2740_, v_a_2741_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2744_, lean_object* v_m_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2745_, v_a_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2748_, lean_object* v_m_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_2748_, v_m_2749_, v_a_2750_);
lean_dec_ref(v_a_2750_);
lean_dec_ref(v_m_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_2752_, lean_object* v_ref_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2753_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2758_, lean_object* v_ref_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2758_, v_ref_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_2774_, lean_object* v_x_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_2781_, v_x_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2788_, lean_object* v_m_2789_, lean_object* v_a_2790_, lean_object* v_b_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2789_, v_a_2790_, v_b_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_2793_, lean_object* v_a_2794_, lean_object* v_x_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2794_, v_x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2797_, lean_object* v_a_2798_, lean_object* v_x_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2797_, v_a_2798_, v_x_2799_);
lean_dec(v_x_2799_);
lean_dec_ref(v_a_2798_);
return v_res_2800_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_2801_, lean_object* v_a_2802_, lean_object* v_x_2803_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2802_, v_x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2805_, lean_object* v_a_2806_, lean_object* v_x_2807_){
_start:
{
uint8_t v_res_2808_; lean_object* v_r_2809_; 
v_res_2808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_2805_, v_a_2806_, v_x_2807_);
lean_dec(v_x_2807_);
lean_dec_ref(v_a_2806_);
v_r_2809_ = lean_box(v_res_2808_);
return v_r_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_2810_, lean_object* v_data_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_data_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_2813_, lean_object* v_a_2814_, lean_object* v_b_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2814_, v_b_2815_, v_x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_2818_, lean_object* v_i_2819_, lean_object* v_source_2820_, lean_object* v_target_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_2819_, v_source_2820_, v_target_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_2824_, v_x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Meta_Sym_foldProjs(v_e_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Meta_Grind_foldProjs(v_e_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_2848_, lean_object* v_config_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_00___x40___internal___hyg_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = lean_grind_normalize(v_e_2848_, v_config_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_);
return v_res_2855_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = lean_box(0);
v___x_2864_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2865_ = l_Lean_mkConst(v___x_2864_, v___x_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_2868_ = l_Lean_Expr_app___override(v___x_2867_, v_e_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2870_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = l_Lean_Expr_isAppOfArity(v_e_2869_, v___x_2870_, v___x_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_2873_){
_start:
{
uint8_t v_res_2874_; lean_object* v_r_2875_; 
v_res_2874_ = l_Lean_Meta_Grind_isMatchCond(v_e_2873_);
lean_dec_ref(v_e_2873_);
v_r_2875_ = lean_box(v_res_2874_);
return v_r_2875_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2883_ = l_Lean_mkConst(v___x_2882_, v___x_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_2884_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_2886_ = l_Lean_Expr_app___override(v___x_2885_, v_e_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_2887_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2888_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = l_Lean_Expr_isAppOfArity(v_e_2887_, v___x_2888_, v___x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_2891_){
_start:
{
uint8_t v_res_2892_; lean_object* v_r_2893_; 
v_res_2892_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_2891_);
lean_dec_ref(v_e_2891_);
v_r_2893_ = lean_box(v_res_2892_);
return v_r_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2899_; 
lean_inc_ref(v_e_2896_);
v___x_2899_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2916_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2916_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2916_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = l_Lean_Expr_cleanupAnnotations(v_a_2900_);
v___x_2910_ = l_Lean_Expr_isApp(v___x_2909_);
if (v___x_2910_ == 0)
{
lean_dec_ref(v___x_2909_);
lean_dec_ref(v_e_2896_);
goto v___jp_2904_;
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2911_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2909_);
v___x_2912_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2913_ = l_Lean_Expr_isConstOf(v___x_2911_, v___x_2912_);
lean_dec_ref(v___x_2911_);
if (v___x_2913_ == 0)
{
lean_dec_ref(v_e_2896_);
goto v___jp_2904_;
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_del_object(v___x_2902_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_e_2896_);
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
v___jp_2904_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = ((lean_object*)(l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0));
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2905_);
v___x_2907_ = v___x_2902_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v_e_2896_);
v_a_2917_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2899_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2899_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_2925_, v_a_2926_);
lean_dec(v_a_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_2929_, v_a_2934_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_2968_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_2969_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2966_, v___x_2967_, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_2977_ = 0;
v___x_2978_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2972_, v___x_2976_, v___x_2977_, v_a_2973_, v_a_2974_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_2979_, v_a_2980_, v_a_2981_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
lean_inc_ref(v_e_2984_);
v___x_2994_ = l_Lean_Expr_cleanupAnnotations(v_e_2984_);
v___x_2995_ = l_Lean_Expr_isApp(v___x_2994_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v___x_2994_);
goto v___jp_2990_;
}
else
{
lean_object* v_arg_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v_arg_2996_ = lean_ctor_get(v___x_2994_, 1);
lean_inc_ref(v_arg_2996_);
v___x_2997_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2994_);
v___x_2998_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2999_ = l_Lean_Expr_isConstOf(v___x_2997_, v___x_2998_);
lean_dec_ref(v___x_2997_);
if (v___x_2999_ == 0)
{
lean_dec_ref(v_arg_2996_);
goto v___jp_2990_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec_ref(v_e_2984_);
v___x_3000_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_2996_);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
return v___x_3003_;
}
}
v___jp_2990_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_e_2984_);
v___x_2992_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* v_e_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_e_3011_);
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_object* v_00_u03b1_3026_, lean_object* v_x_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_apply_1(v_x_3027_, lean_box(0));
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3035_, lean_object* v_x_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(v_00_u03b1_3035_, v_x_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___y_3051_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; uint8_t v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; uint8_t v___y_3077_; lean_object* v_fileName_3083_; lean_object* v_fileMap_3084_; lean_object* v_options_3085_; lean_object* v_currRecDepth_3086_; lean_object* v_maxRecDepth_3087_; lean_object* v_ref_3088_; lean_object* v_currNamespace_3089_; lean_object* v_openDecls_3090_; lean_object* v_initHeartbeats_3091_; lean_object* v_maxHeartbeats_3092_; lean_object* v_quotContext_3093_; lean_object* v_currMacroScope_3094_; uint8_t v_diag_3095_; lean_object* v_cancelTk_x3f_3096_; uint8_t v_suppressElabErrors_3097_; lean_object* v_inheritedTraceOptions_3098_; 
v_fileName_3083_ = lean_ctor_get(v___y_3047_, 0);
v_fileMap_3084_ = lean_ctor_get(v___y_3047_, 1);
v_options_3085_ = lean_ctor_get(v___y_3047_, 2);
v_currRecDepth_3086_ = lean_ctor_get(v___y_3047_, 3);
v_maxRecDepth_3087_ = lean_ctor_get(v___y_3047_, 4);
v_ref_3088_ = lean_ctor_get(v___y_3047_, 5);
v_currNamespace_3089_ = lean_ctor_get(v___y_3047_, 6);
v_openDecls_3090_ = lean_ctor_get(v___y_3047_, 7);
v_initHeartbeats_3091_ = lean_ctor_get(v___y_3047_, 8);
v_maxHeartbeats_3092_ = lean_ctor_get(v___y_3047_, 9);
v_quotContext_3093_ = lean_ctor_get(v___y_3047_, 10);
v_currMacroScope_3094_ = lean_ctor_get(v___y_3047_, 11);
v_diag_3095_ = lean_ctor_get_uint8(v___y_3047_, sizeof(void*)*14);
v_cancelTk_x3f_3096_ = lean_ctor_get(v___y_3047_, 12);
v_suppressElabErrors_3097_ = lean_ctor_get_uint8(v___y_3047_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3098_ = lean_ctor_get(v___y_3047_, 13);
if (lean_obj_tag(v_cancelTk_x3f_3096_) == 1)
{
lean_object* v_val_3104_; uint8_t v___x_3105_; 
v_val_3104_ = lean_ctor_get(v_cancelTk_x3f_3096_, 0);
v___x_3105_ = l_IO_CancelToken_isSet(v_val_3104_);
if (v___x_3105_ == 0)
{
goto v___jp_3099_;
}
else
{
lean_object* v___x_3106_; lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref(v_x_3043_);
v___x_3106_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
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
goto v___jp_3099_;
}
v___jp_3050_:
{
if (lean_obj_tag(v___y_3051_) == 0)
{
return v___y_3051_;
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3052_ = lean_ctor_get(v___y_3051_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___y_3051_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___y_3051_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___y_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
v___jp_3060_:
{
if (v___y_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3078_ = lean_unsigned_to_nat(1u);
v___x_3079_ = lean_nat_add(v___y_3067_, v___x_3078_);
lean_inc_ref(v___y_3061_);
lean_inc(v___y_3074_);
lean_inc(v___y_3066_);
lean_inc(v___y_3069_);
lean_inc(v___y_3065_);
lean_inc(v___y_3076_);
lean_inc(v___y_3070_);
lean_inc(v___y_3063_);
lean_inc(v___y_3075_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3062_);
lean_inc_ref(v___y_3072_);
lean_inc_ref(v___y_3068_);
v___x_3080_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3080_, 0, v___y_3068_);
lean_ctor_set(v___x_3080_, 1, v___y_3072_);
lean_ctor_set(v___x_3080_, 2, v___y_3062_);
lean_ctor_set(v___x_3080_, 3, v___x_3079_);
lean_ctor_set(v___x_3080_, 4, v___y_3064_);
lean_ctor_set(v___x_3080_, 5, v___y_3075_);
lean_ctor_set(v___x_3080_, 6, v___y_3063_);
lean_ctor_set(v___x_3080_, 7, v___y_3070_);
lean_ctor_set(v___x_3080_, 8, v___y_3076_);
lean_ctor_set(v___x_3080_, 9, v___y_3065_);
lean_ctor_set(v___x_3080_, 10, v___y_3069_);
lean_ctor_set(v___x_3080_, 11, v___y_3066_);
lean_ctor_set(v___x_3080_, 12, v___y_3074_);
lean_ctor_set(v___x_3080_, 13, v___y_3061_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*14, v___y_3073_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*14 + 1, v___y_3071_);
lean_inc(v___y_3048_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3045_);
lean_inc(v___y_3044_);
v___x_3081_ = lean_apply_6(v_x_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___x_3080_, v___y_3048_, lean_box(0));
v___y_3051_ = v___x_3081_;
goto v___jp_3050_;
}
else
{
lean_object* v___x_3082_; 
lean_dec_ref(v_x_3043_);
lean_inc(v___y_3075_);
v___x_3082_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v___y_3075_);
v___y_3051_ = v___x_3082_;
goto v___jp_3050_;
}
}
v___jp_3099_:
{
lean_object* v___x_3100_; uint8_t v___x_3101_; uint8_t v___x_3102_; 
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = lean_nat_dec_eq(v_maxRecDepth_3087_, v___x_3100_);
v___x_3102_ = lean_bool_not(v___x_3101_);
if (v___x_3102_ == 0)
{
v___y_3061_ = v_inheritedTraceOptions_3098_;
v___y_3062_ = v_options_3085_;
v___y_3063_ = v_currNamespace_3089_;
v___y_3064_ = v_maxRecDepth_3087_;
v___y_3065_ = v_maxHeartbeats_3092_;
v___y_3066_ = v_currMacroScope_3094_;
v___y_3067_ = v_currRecDepth_3086_;
v___y_3068_ = v_fileName_3083_;
v___y_3069_ = v_quotContext_3093_;
v___y_3070_ = v_openDecls_3090_;
v___y_3071_ = v_suppressElabErrors_3097_;
v___y_3072_ = v_fileMap_3084_;
v___y_3073_ = v_diag_3095_;
v___y_3074_ = v_cancelTk_x3f_3096_;
v___y_3075_ = v_ref_3088_;
v___y_3076_ = v_initHeartbeats_3091_;
v___y_3077_ = v___x_3102_;
goto v___jp_3060_;
}
else
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_nat_dec_eq(v_currRecDepth_3086_, v_maxRecDepth_3087_);
v___y_3061_ = v_inheritedTraceOptions_3098_;
v___y_3062_ = v_options_3085_;
v___y_3063_ = v_currNamespace_3089_;
v___y_3064_ = v_maxRecDepth_3087_;
v___y_3065_ = v_maxHeartbeats_3092_;
v___y_3066_ = v_currMacroScope_3094_;
v___y_3067_ = v_currRecDepth_3086_;
v___y_3068_ = v_fileName_3083_;
v___y_3069_ = v_quotContext_3093_;
v___y_3070_ = v_openDecls_3090_;
v___y_3071_ = v_suppressElabErrors_3097_;
v___y_3072_ = v_fileMap_3084_;
v___y_3073_ = v_diag_3095_;
v___y_3074_ = v_cancelTk_x3f_3096_;
v___y_3075_ = v_ref_3088_;
v___y_3076_ = v_initHeartbeats_3091_;
v___y_3077_ = v___x_3103_;
goto v___jp_3060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_3123_, lean_object* v_x_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_apply_1(v_x_3124_, lean_box(0));
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_x_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(v_00_u03b1_3132_, v_x_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_3140_, lean_object* v_post_3141_, size_t v_sz_3142_, size_t v_i_3143_, lean_object* v_bs_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_usize_dec_lt(v_i_3143_, v_sz_3142_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref(v_post_3141_);
lean_dec_ref(v_pre_3140_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_bs_3144_);
return v___x_3152_;
}
else
{
lean_object* v_v_3153_; lean_object* v___x_3154_; 
v_v_3153_ = lean_array_uget_borrowed(v_bs_3144_, v_i_3143_);
lean_inc(v_v_3153_);
lean_inc_ref(v_post_3141_);
lean_inc_ref(v_pre_3140_);
v___x_3154_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3140_, v_post_3141_, v_v_3153_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v_bs_x27_3157_; size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = lean_unsigned_to_nat(0u);
v_bs_x27_3157_ = lean_array_uset(v_bs_3144_, v_i_3143_, v___x_3156_);
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3143_, v___x_3158_);
v___x_3160_ = lean_array_uset(v_bs_x27_3157_, v_i_3143_, v_a_3155_);
v_i_3143_ = v___x_3159_;
v_bs_3144_ = v___x_3160_;
goto _start;
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v_bs_3144_);
lean_dec_ref(v_post_3141_);
lean_dec_ref(v_pre_3140_);
v_a_3162_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3154_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3154_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_3170_, lean_object* v_post_3171_, lean_object* v_x_3172_, lean_object* v_x_3173_, lean_object* v_x_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
if (lean_obj_tag(v_x_3172_) == 5)
{
lean_object* v_fn_3181_; lean_object* v_arg_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_fn_3181_ = lean_ctor_get(v_x_3172_, 0);
lean_inc_ref(v_fn_3181_);
v_arg_3182_ = lean_ctor_get(v_x_3172_, 1);
lean_inc_ref(v_arg_3182_);
lean_dec_ref_known(v_x_3172_, 2);
v___x_3183_ = lean_array_set(v_x_3173_, v_x_3174_, v_arg_3182_);
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = lean_nat_sub(v_x_3174_, v___x_3184_);
lean_dec(v_x_3174_);
v_x_3172_ = v_fn_3181_;
v_x_3173_ = v___x_3183_;
v_x_3174_ = v___x_3185_;
goto _start;
}
else
{
lean_object* v___x_3187_; 
lean_dec(v_x_3174_);
lean_inc_ref(v_post_3171_);
lean_inc_ref(v_pre_3170_);
v___x_3187_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3170_, v_post_3171_, v_x_3172_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; size_t v_sz_3189_; size_t v___x_3190_; lean_object* v___x_3191_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v_sz_3189_ = lean_array_size(v_x_3173_);
v___x_3190_ = ((size_t)0ULL);
lean_inc_ref(v_post_3171_);
lean_inc_ref(v_pre_3170_);
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3170_, v_post_3171_, v_sz_3189_, v___x_3190_, v_x_3173_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3191_, 1);
v___x_3193_ = l_Lean_mkAppN(v_a_3188_, v_a_3192_);
lean_dec(v_a_3192_);
v___x_3194_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3170_, v_post_3171_, v___x_3193_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3194_;
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_3188_);
lean_dec_ref(v_post_3171_);
lean_dec_ref(v_pre_3170_);
v_a_3195_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3191_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3191_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_dec_ref(v_x_3173_);
lean_dec_ref(v_post_3171_);
lean_dec_ref(v_pre_3170_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v___x_3203_, lean_object* v_pre_3204_, lean_object* v_e_3205_, lean_object* v_post_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___y_3214_; lean_object* v___y_3215_; uint8_t v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3221_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; uint8_t v___y_3236_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; uint8_t v___y_3249_; lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_Core_checkSystem(v___x_3203_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v___x_3257_; 
lean_dec_ref_known(v___x_3256_, 1);
lean_inc_ref(v_pre_3204_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc_ref(v_e_3205_);
v___x_3257_ = lean_apply_6(v_pre_3204_, v_e_3205_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, lean_box(0));
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3347_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3347_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3347_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___y_3263_; 
switch(lean_obj_tag(v_a_3258_))
{
case 0:
{
lean_object* v_e_3337_; lean_object* v___x_3339_; 
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_e_3205_);
lean_dec_ref(v_pre_3204_);
v_e_3337_ = lean_ctor_get(v_a_3258_, 0);
lean_inc_ref(v_e_3337_);
lean_dec_ref_known(v_a_3258_, 1);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v_e_3337_);
v___x_3339_ = v___x_3260_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_e_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
case 1:
{
lean_object* v_e_3341_; lean_object* v___x_3342_; 
lean_del_object(v___x_3260_);
lean_dec_ref(v_e_3205_);
v_e_3341_ = lean_ctor_get(v_a_3258_, 0);
lean_inc_ref(v_e_3341_);
lean_dec_ref_known(v_a_3258_, 1);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3342_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_e_3341_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v_a_3343_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3344_;
}
else
{
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3342_;
}
}
default: 
{
lean_object* v_e_x3f_3345_; 
lean_del_object(v___x_3260_);
v_e_x3f_3345_ = lean_ctor_get(v_a_3258_, 0);
lean_inc(v_e_x3f_3345_);
lean_dec_ref_known(v_a_3258_, 1);
if (lean_obj_tag(v_e_x3f_3345_) == 0)
{
v___y_3263_ = v_e_3205_;
goto v___jp_3262_;
}
else
{
lean_object* v_val_3346_; 
lean_dec_ref(v_e_3205_);
v_val_3346_ = lean_ctor_get(v_e_x3f_3345_, 0);
lean_inc(v_val_3346_);
lean_dec_ref_known(v_e_x3f_3345_, 1);
v___y_3263_ = v_val_3346_;
goto v___jp_3262_;
}
}
}
v___jp_3262_:
{
switch(lean_obj_tag(v___y_3263_))
{
case 7:
{
lean_object* v_binderName_3264_; lean_object* v_binderType_3265_; lean_object* v_body_3266_; uint8_t v_binderInfo_3267_; lean_object* v___x_3268_; 
v_binderName_3264_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_binderName_3264_);
v_binderType_3265_ = lean_ctor_get(v___y_3263_, 1);
v_body_3266_ = lean_ctor_get(v___y_3263_, 2);
v_binderInfo_3267_ = lean_ctor_get_uint8(v___y_3263_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3265_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3268_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_binderType_3265_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
lean_inc_ref(v_body_3266_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3270_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_body_3266_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; size_t v___x_3272_; size_t v___x_3273_; uint8_t v___x_3274_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = lean_ptr_addr(v_binderType_3265_);
v___x_3273_ = lean_ptr_addr(v_a_3269_);
v___x_3274_ = lean_usize_dec_eq(v___x_3272_, v___x_3273_);
if (v___x_3274_ == 0)
{
v___y_3244_ = v_binderInfo_3267_;
v___y_3245_ = v___y_3263_;
v___y_3246_ = v_a_3269_;
v___y_3247_ = v_binderName_3264_;
v___y_3248_ = v_a_3271_;
v___y_3249_ = v___x_3274_;
goto v___jp_3243_;
}
else
{
size_t v___x_3275_; size_t v___x_3276_; uint8_t v___x_3277_; 
v___x_3275_ = lean_ptr_addr(v_body_3266_);
v___x_3276_ = lean_ptr_addr(v_a_3271_);
v___x_3277_ = lean_usize_dec_eq(v___x_3275_, v___x_3276_);
v___y_3244_ = v_binderInfo_3267_;
v___y_3245_ = v___y_3263_;
v___y_3246_ = v_a_3269_;
v___y_3247_ = v_binderName_3264_;
v___y_3248_ = v_a_3271_;
v___y_3249_ = v___x_3277_;
goto v___jp_3243_;
}
}
else
{
lean_dec(v_a_3269_);
lean_dec(v_binderName_3264_);
lean_dec_ref_known(v___y_3263_, 3);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3270_;
}
}
else
{
lean_dec(v_binderName_3264_);
lean_dec_ref_known(v___y_3263_, 3);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3268_;
}
}
case 6:
{
lean_object* v_binderName_3278_; lean_object* v_binderType_3279_; lean_object* v_body_3280_; uint8_t v_binderInfo_3281_; lean_object* v___x_3282_; 
v_binderName_3278_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_binderName_3278_);
v_binderType_3279_ = lean_ctor_get(v___y_3263_, 1);
v_body_3280_ = lean_ctor_get(v___y_3263_, 2);
v_binderInfo_3281_ = lean_ctor_get_uint8(v___y_3263_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3279_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3282_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_binderType_3279_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3284_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
lean_inc_ref(v_body_3280_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3284_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_body_3280_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; size_t v___x_3286_; size_t v___x_3287_; uint8_t v___x_3288_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = lean_ptr_addr(v_binderType_3279_);
v___x_3287_ = lean_ptr_addr(v_a_3283_);
v___x_3288_ = lean_usize_dec_eq(v___x_3286_, v___x_3287_);
if (v___x_3288_ == 0)
{
v___y_3231_ = v___y_3263_;
v___y_3232_ = v_binderName_3278_;
v___y_3233_ = v_binderInfo_3281_;
v___y_3234_ = v_a_3283_;
v___y_3235_ = v_a_3285_;
v___y_3236_ = v___x_3288_;
goto v___jp_3230_;
}
else
{
size_t v___x_3289_; size_t v___x_3290_; uint8_t v___x_3291_; 
v___x_3289_ = lean_ptr_addr(v_body_3280_);
v___x_3290_ = lean_ptr_addr(v_a_3285_);
v___x_3291_ = lean_usize_dec_eq(v___x_3289_, v___x_3290_);
v___y_3231_ = v___y_3263_;
v___y_3232_ = v_binderName_3278_;
v___y_3233_ = v_binderInfo_3281_;
v___y_3234_ = v_a_3283_;
v___y_3235_ = v_a_3285_;
v___y_3236_ = v___x_3291_;
goto v___jp_3230_;
}
}
else
{
lean_dec(v_a_3283_);
lean_dec(v_binderName_3278_);
lean_dec_ref_known(v___y_3263_, 3);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3284_;
}
}
else
{
lean_dec(v_binderName_3278_);
lean_dec_ref_known(v___y_3263_, 3);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3282_;
}
}
case 8:
{
lean_object* v_declName_3292_; lean_object* v_type_3293_; lean_object* v_value_3294_; lean_object* v_body_3295_; uint8_t v_nondep_3296_; lean_object* v___x_3297_; 
v_declName_3292_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_declName_3292_);
v_type_3293_ = lean_ctor_get(v___y_3263_, 1);
v_value_3294_ = lean_ctor_get(v___y_3263_, 2);
v_body_3295_ = lean_ctor_get(v___y_3263_, 3);
lean_inc_ref(v_body_3295_);
v_nondep_3296_ = lean_ctor_get_uint8(v___y_3263_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3293_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3297_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_type_3293_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
lean_inc_ref(v_value_3294_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3299_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_value_3294_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
lean_inc_ref(v_body_3295_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3301_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_body_3295_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; size_t v___x_3303_; size_t v___x_3304_; uint8_t v___x_3305_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = lean_ptr_addr(v_type_3293_);
v___x_3304_ = lean_ptr_addr(v_a_3298_);
v___x_3305_ = lean_usize_dec_eq(v___x_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
v___y_3214_ = v___y_3263_;
v___y_3215_ = v_body_3295_;
v___y_3216_ = v_nondep_3296_;
v___y_3217_ = v_a_3300_;
v___y_3218_ = v_a_3298_;
v___y_3219_ = v_a_3302_;
v___y_3220_ = v_declName_3292_;
v___y_3221_ = v___x_3305_;
goto v___jp_3213_;
}
else
{
size_t v___x_3306_; size_t v___x_3307_; uint8_t v___x_3308_; 
v___x_3306_ = lean_ptr_addr(v_value_3294_);
v___x_3307_ = lean_ptr_addr(v_a_3300_);
v___x_3308_ = lean_usize_dec_eq(v___x_3306_, v___x_3307_);
v___y_3214_ = v___y_3263_;
v___y_3215_ = v_body_3295_;
v___y_3216_ = v_nondep_3296_;
v___y_3217_ = v_a_3300_;
v___y_3218_ = v_a_3298_;
v___y_3219_ = v_a_3302_;
v___y_3220_ = v_declName_3292_;
v___y_3221_ = v___x_3308_;
goto v___jp_3213_;
}
}
else
{
lean_dec(v_a_3300_);
lean_dec(v_a_3298_);
lean_dec_ref(v_body_3295_);
lean_dec(v_declName_3292_);
lean_dec_ref_known(v___y_3263_, 4);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3301_;
}
}
else
{
lean_dec(v_a_3298_);
lean_dec_ref(v_body_3295_);
lean_dec(v_declName_3292_);
lean_dec_ref_known(v___y_3263_, 4);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3299_;
}
}
else
{
lean_dec_ref(v_body_3295_);
lean_dec(v_declName_3292_);
lean_dec_ref_known(v___y_3263_, 4);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3297_;
}
}
case 5:
{
lean_object* v_dummy_3309_; lean_object* v_nargs_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_dummy_3309_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3310_ = l_Lean_Expr_getAppNumArgs(v___y_3263_);
lean_inc(v_nargs_3310_);
v___x_3311_ = lean_mk_array(v_nargs_3310_, v_dummy_3309_);
v___x_3312_ = lean_unsigned_to_nat(1u);
v___x_3313_ = lean_nat_sub(v_nargs_3310_, v___x_3312_);
lean_dec(v_nargs_3310_);
v___x_3314_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3204_, v_post_3206_, v___y_3263_, v___x_3311_, v___x_3313_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3314_;
}
case 10:
{
lean_object* v_data_3315_; lean_object* v_expr_3316_; lean_object* v___x_3317_; 
v_data_3315_ = lean_ctor_get(v___y_3263_, 0);
v_expr_3316_ = lean_ctor_get(v___y_3263_, 1);
lean_inc_ref(v_expr_3316_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3317_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_expr_3316_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; size_t v___x_3319_; size_t v___x_3320_; uint8_t v___x_3321_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = lean_ptr_addr(v_expr_3316_);
v___x_3320_ = lean_ptr_addr(v_a_3318_);
v___x_3321_ = lean_usize_dec_eq(v___x_3319_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_inc(v_data_3315_);
lean_dec_ref_known(v___y_3263_, 2);
v___x_3322_ = l_Lean_Expr_mdata___override(v_data_3315_, v_a_3318_);
v___x_3323_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3322_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; 
lean_dec(v_a_3318_);
v___x_3324_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___y_3263_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3324_;
}
}
else
{
lean_dec_ref_known(v___y_3263_, 2);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3317_;
}
}
case 11:
{
lean_object* v_typeName_3325_; lean_object* v_idx_3326_; lean_object* v_struct_3327_; lean_object* v___x_3328_; 
v_typeName_3325_ = lean_ctor_get(v___y_3263_, 0);
v_idx_3326_ = lean_ctor_get(v___y_3263_, 1);
v_struct_3327_ = lean_ctor_get(v___y_3263_, 2);
lean_inc_ref(v_struct_3327_);
lean_inc_ref(v_post_3206_);
lean_inc_ref(v_pre_3204_);
v___x_3328_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3204_, v_post_3206_, v_struct_3327_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; size_t v___x_3330_; size_t v___x_3331_; uint8_t v___x_3332_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3330_ = lean_ptr_addr(v_struct_3327_);
v___x_3331_ = lean_ptr_addr(v_a_3329_);
v___x_3332_ = lean_usize_dec_eq(v___x_3330_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_inc(v_idx_3326_);
lean_inc(v_typeName_3325_);
lean_dec_ref_known(v___y_3263_, 3);
v___x_3333_ = l_Lean_Expr_proj___override(v_typeName_3325_, v_idx_3326_, v_a_3329_);
v___x_3334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3333_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; 
lean_dec(v_a_3329_);
v___x_3335_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___y_3263_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3335_;
}
}
else
{
lean_dec_ref_known(v___y_3263_, 3);
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_pre_3204_);
return v___x_3328_;
}
}
default: 
{
lean_object* v___x_3336_; 
v___x_3336_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___y_3263_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3336_;
}
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_e_3205_);
lean_dec_ref(v_pre_3204_);
v_a_3348_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3257_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3257_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec_ref(v_post_3206_);
lean_dec_ref(v_e_3205_);
lean_dec_ref(v_pre_3204_);
v_a_3356_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3256_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3256_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
v___jp_3213_:
{
if (v___y_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___y_3214_);
v___x_3222_ = l_Lean_Expr_letE___override(v___y_3220_, v___y_3218_, v___y_3217_, v___y_3219_, v___y_3216_);
v___x_3223_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3222_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3223_;
}
else
{
size_t v___x_3224_; size_t v___x_3225_; uint8_t v___x_3226_; 
v___x_3224_ = lean_ptr_addr(v___y_3215_);
lean_dec_ref(v___y_3215_);
v___x_3225_ = lean_ptr_addr(v___y_3219_);
v___x_3226_ = lean_usize_dec_eq(v___x_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_dec_ref(v___y_3214_);
v___x_3227_ = l_Lean_Expr_letE___override(v___y_3220_, v___y_3218_, v___y_3217_, v___y_3219_, v___y_3216_);
v___x_3228_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3227_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; 
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec_ref(v___y_3217_);
v___x_3229_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___y_3214_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3229_;
}
}
}
v___jp_3230_:
{
if (v___y_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec_ref(v___y_3231_);
v___x_3237_ = l_Lean_Expr_lam___override(v___y_3232_, v___y_3234_, v___y_3235_, v___y_3233_);
v___x_3238_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3237_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3238_;
}
else
{
uint8_t v___x_3239_; 
v___x_3239_ = l_Lean_instBEqBinderInfo_beq(v___y_3233_, v___y_3233_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_dec_ref(v___y_3231_);
v___x_3240_ = l_Lean_Expr_lam___override(v___y_3232_, v___y_3234_, v___y_3235_, v___y_3233_);
v___x_3241_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3240_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3232_);
v___x_3242_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___y_3231_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3242_;
}
}
}
v___jp_3243_:
{
if (v___y_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec_ref(v___y_3245_);
v___x_3250_ = l_Lean_Expr_forallE___override(v___y_3247_, v___y_3246_, v___y_3248_, v___y_3244_);
v___x_3251_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3250_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3251_;
}
else
{
uint8_t v___x_3252_; 
v___x_3252_ = l_Lean_instBEqBinderInfo_beq(v___y_3244_, v___y_3244_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
lean_dec_ref(v___y_3245_);
v___x_3253_ = l_Lean_Expr_forallE___override(v___y_3247_, v___y_3246_, v___y_3248_, v___y_3244_);
v___x_3254_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___x_3253_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3254_;
}
else
{
lean_object* v___x_3255_; 
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
v___x_3255_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3204_, v_post_3206_, v___y_3245_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v___x_3364_, lean_object* v_pre_3365_, lean_object* v_e_3366_, lean_object* v_post_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_3364_, v_pre_3365_, v_e_3366_, v_post_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_3375_, lean_object* v_post_3376_, lean_object* v_e_3377_, lean_object* v_a_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_inc(v_a_3378_);
v___x_3384_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3384_, 0, lean_box(0));
lean_closure_set(v___x_3384_, 1, lean_box(0));
lean_closure_set(v___x_3384_, 2, v_a_3378_);
v___x_3385_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___x_3384_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3417_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3417_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3417_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3386_, v_e_3377_);
lean_dec(v_a_3386_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v___x_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; 
lean_del_object(v___x_3388_);
v___x_3391_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_3377_);
v___f_3392_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3392_, 0, v___x_3391_);
lean_closure_set(v___f_3392_, 1, v_pre_3375_);
lean_closure_set(v___f_3392_, 2, v_e_3377_);
lean_closure_set(v___f_3392_, 3, v_post_3376_);
v___x_3393_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_3392_, v_a_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___f_3395_; lean_object* v___x_3396_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc_n(v_a_3394_, 2);
lean_dec_ref_known(v___x_3393_, 1);
lean_inc(v_a_3378_);
v___f_3395_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3395_, 0, v_a_3378_);
lean_closure_set(v___f_3395_, 1, v_e_3377_);
lean_closure_set(v___f_3395_, 2, v_a_3394_);
v___x_3396_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___f_3395_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v___x_3396_, 0);
lean_dec(v_unused_3404_);
v___x_3398_ = v___x_3396_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_dec(v___x_3396_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v_a_3394_);
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3394_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v_a_3394_);
v_a_3405_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3396_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3396_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_dec_ref(v_e_3377_);
return v___x_3393_;
}
}
else
{
lean_object* v_val_3413_; lean_object* v___x_3415_; 
lean_dec_ref(v_e_3377_);
lean_dec_ref(v_post_3376_);
lean_dec_ref(v_pre_3375_);
v_val_3413_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_val_3413_);
lean_dec_ref_known(v___x_3390_, 1);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v_val_3413_);
v___x_3415_ = v___x_3388_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_val_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v_e_3377_);
lean_dec_ref(v_post_3376_);
lean_dec_ref(v_pre_3375_);
v_a_3418_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3385_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3385_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_3426_, lean_object* v_post_3427_, lean_object* v_e_3428_, lean_object* v_a_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; 
lean_inc_ref(v_post_3427_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc_ref(v_e_3428_);
v___x_3435_ = lean_apply_6(v_post_3427_, v_e_3428_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, lean_box(0));
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3454_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3454_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3454_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
switch(lean_obj_tag(v_a_3436_))
{
case 0:
{
lean_object* v_e_3440_; lean_object* v___x_3442_; 
lean_dec_ref(v_e_3428_);
lean_dec_ref(v_post_3427_);
lean_dec_ref(v_pre_3426_);
v_e_3440_ = lean_ctor_get(v_a_3436_, 0);
lean_inc_ref(v_e_3440_);
lean_dec_ref_known(v_a_3436_, 1);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v_e_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_e_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
case 1:
{
lean_object* v_e_3444_; lean_object* v___x_3445_; 
lean_del_object(v___x_3438_);
lean_dec_ref(v_e_3428_);
v_e_3444_ = lean_ctor_get(v_a_3436_, 0);
lean_inc_ref(v_e_3444_);
lean_dec_ref_known(v_a_3436_, 1);
v___x_3445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3426_, v_post_3427_, v_e_3444_, v_a_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3445_;
}
default: 
{
lean_object* v_e_x3f_3446_; 
lean_dec_ref(v_post_3427_);
lean_dec_ref(v_pre_3426_);
v_e_x3f_3446_ = lean_ctor_get(v_a_3436_, 0);
lean_inc(v_e_x3f_3446_);
lean_dec_ref_known(v_a_3436_, 1);
if (lean_obj_tag(v_e_x3f_3446_) == 0)
{
lean_object* v___x_3448_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v_e_3428_);
v___x_3448_ = v___x_3438_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_e_3428_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
else
{
lean_object* v_val_3450_; lean_object* v___x_3452_; 
lean_dec_ref(v_e_3428_);
v_val_3450_ = lean_ctor_get(v_e_x3f_3446_, 0);
lean_inc(v_val_3450_);
lean_dec_ref_known(v_e_x3f_3446_, 1);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v_val_3450_);
v___x_3452_ = v___x_3438_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_val_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec_ref(v_e_3428_);
lean_dec_ref(v_post_3427_);
lean_dec_ref(v_pre_3426_);
v_a_3455_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3435_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3435_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_3463_, lean_object* v_post_3464_, lean_object* v_e_3465_, lean_object* v_a_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3463_, v_post_3464_, v_e_3465_, v_a_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v_a_3466_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_3473_, lean_object* v_post_3474_, lean_object* v_sz_3475_, lean_object* v_i_3476_, lean_object* v_bs_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
size_t v_sz_boxed_3484_; size_t v_i_boxed_3485_; lean_object* v_res_3486_; 
v_sz_boxed_3484_ = lean_unbox_usize(v_sz_3475_);
lean_dec(v_sz_3475_);
v_i_boxed_3485_ = lean_unbox_usize(v_i_3476_);
lean_dec(v_i_3476_);
v_res_3486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3473_, v_post_3474_, v_sz_boxed_3484_, v_i_boxed_3485_, v_bs_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_3487_, lean_object* v_post_3488_, lean_object* v_x_3489_, lean_object* v_x_3490_, lean_object* v_x_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3487_, v_post_3488_, v_x_3489_, v_x_3490_, v_x_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_3499_, lean_object* v_post_3500_, lean_object* v_e_3501_, lean_object* v_a_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3499_, v_post_3500_, v_e_3501_, v_a_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v_a_3502_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_3509_, lean_object* v_pre_3510_, lean_object* v_post_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v_a_3519_; lean_object* v___x_3520_; 
v___x_3517_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_3518_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3517_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3510_, v_post_3511_, v_input_3509_, v_a_3519_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v___x_3522_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3522_, 0, lean_box(0));
lean_closure_set(v___x_3522_, 1, lean_box(0));
lean_closure_set(v___x_3522_, 2, v_a_3519_);
v___x_3523_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3522_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v___x_3523_, 0);
lean_dec(v_unused_3531_);
v___x_3525_ = v___x_3523_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v___x_3523_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_a_3521_);
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3521_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
else
{
lean_dec(v_a_3519_);
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_3532_, lean_object* v_pre_3533_, lean_object* v_post_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_3532_, v_pre_3533_, v_post_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_3551_ = lean_find_expr(v___x_3550_, v_e_3544_);
if (lean_obj_tag(v___x_3551_) == 0)
{
uint8_t v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = 1;
v___x_3553_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3553_, 0, v_e_3544_);
lean_ctor_set(v___x_3553_, 1, v___x_3551_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*2, v___x_3552_);
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
else
{
lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3603_; 
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3551_, 0);
lean_dec(v_unused_3604_);
v___x_3556_ = v___x_3551_;
v_isShared_3557_ = v_isSharedCheck_3603_;
goto v_resetjp_3555_;
}
else
{
lean_dec(v___x_3551_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3603_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v_pre_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; 
v_pre_3558_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_3559_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
lean_inc_ref(v_e_3544_);
v___x_3560_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_3544_, v_pre_3558_, v___f_3559_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_n(v_a_3561_, 2);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = l_Lean_Meta_mkEqRefl(v_a_3561_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3564_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3562_, 1);
lean_inc(v_a_3561_);
v___x_3564_ = l_Lean_Meta_mkEq(v_e_3544_, v_a_3561_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3578_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
uint8_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = 1;
v___x_3570_ = l_Lean_Meta_mkExpectedPropHint(v_a_3563_, v_a_3565_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3570_);
v___x_3572_ = v___x_3556_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3573_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3573_, 0, v_a_3561_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
lean_ctor_set_uint8(v___x_3573_, sizeof(void*)*2, v___x_3569_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3573_);
v___x_3575_ = v___x_3567_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v_a_3563_);
lean_dec(v_a_3561_);
lean_del_object(v___x_3556_);
v_a_3579_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3564_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3564_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v_a_3561_);
lean_del_object(v___x_3556_);
lean_dec_ref(v_e_3544_);
v_a_3587_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3562_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3562_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_del_object(v___x_3556_);
lean_dec_ref(v_e_3544_);
v_a_3595_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3560_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3560_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3612_, lean_object* v_x_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3621_, lean_object* v_x_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_3621_, v_x_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
return v_res_3629_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_3633_){
_start:
{
lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_3635_ = l_Lean_Expr_isAppOf(v_e_3633_, v___x_3634_);
if (v___x_3635_ == 0)
{
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3636_ = lean_unsigned_to_nat(5u);
v___x_3637_ = l_Lean_Expr_getAppNumArgs(v_e_3633_);
v___x_3638_ = lean_nat_dec_le(v___x_3636_, v___x_3637_);
lean_dec(v___x_3637_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_3639_){
_start:
{
uint8_t v_res_3640_; lean_object* v_r_3641_; 
v_res_3640_ = l_Lean_Meta_Grind_isIte(v_e_3639_);
lean_dec_ref(v_e_3639_);
v_r_3641_ = lean_box(v_res_3640_);
return v_r_3641_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_3645_){
_start:
{
lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_3647_ = l_Lean_Expr_isAppOf(v_e_3645_, v___x_3646_);
if (v___x_3647_ == 0)
{
return v___x_3647_;
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3648_ = lean_unsigned_to_nat(5u);
v___x_3649_ = l_Lean_Expr_getAppNumArgs(v_e_3645_);
v___x_3650_ = lean_nat_dec_le(v___x_3648_, v___x_3649_);
lean_dec(v___x_3649_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_3651_){
_start:
{
uint8_t v_res_3652_; lean_object* v_r_3653_; 
v_res_3652_ = l_Lean_Meta_Grind_isDIte(v_e_3651_);
lean_dec_ref(v_e_3651_);
v_r_3653_ = lean_box(v_res_3652_);
return v_r_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_3654_){
_start:
{
uint8_t v___x_3655_; uint8_t v___x_3656_; 
v___x_3655_ = l_Lean_Expr_isApp(v_e_3654_);
v___x_3656_ = lean_bool_not(v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v_f_3657_; uint8_t v___x_3658_; uint8_t v___x_3659_; 
v_f_3657_ = l_Lean_Expr_appFn_x21(v_e_3654_);
v___x_3658_ = l_Lean_Expr_isApp(v_f_3657_);
v___x_3659_ = lean_bool_not(v___x_3658_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = l_Lean_Expr_appFn_x21(v_f_3657_);
lean_dec_ref(v_f_3657_);
v___x_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
return v___x_3661_;
}
else
{
lean_object* v___x_3662_; 
lean_dec_ref(v_f_3657_);
v___x_3662_ = lean_box(0);
return v___x_3662_;
}
}
else
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_box(0);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Meta_Grind_getBinOp(v_e_3664_);
lean_dec_ref(v_e_3664_);
return v_res_3665_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
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
