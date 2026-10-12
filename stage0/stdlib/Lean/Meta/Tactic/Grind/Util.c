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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* l_instMonadEIO___redArg();
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
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
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__4(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__3));
v___x_53_ = l_Lean_MessageData_ofFormat(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_MVarId_ensureNoMVar___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&l_Lean_MVarId_ensureNoMVar___closed__4, &l_Lean_MVarId_ensureNoMVar___closed__4_once, _init_l_Lean_MVarId_ensureNoMVar___closed__4);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
lean_object* l_Lean_MVarId_ensureNoMVar(lean_object* v_mvarId_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; 
lean_inc(v_mvarId_56_);
v___x_62_ = l_Lean_MVarId_getType(v_mvarId_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_77_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_62_, 1);
v___x_64_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_63_, v_a_58_);
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_77_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_Expr_hasExprMVar(v_a_65_);
lean_dec(v_a_65_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_72_; 
lean_dec(v_mvarId_56_);
v___x_70_ = lean_box(0);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_70_);
v___x_72_ = v___x_67_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
lean_del_object(v___x_67_);
v___x_74_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_75_ = lean_obj_once(&l_Lean_MVarId_ensureNoMVar___closed__5, &l_Lean_MVarId_ensureNoMVar___closed__5_once, _init_l_Lean_MVarId_ensureNoMVar___closed__5);
v___x_76_ = l_Lean_Meta_throwTacticEx___redArg(v___x_74_, v_mvarId_56_, v___x_75_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v___x_76_;
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_dec(v_mvarId_56_);
v_a_78_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_62_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_62_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_ensureNoMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_56_ = stack[0].m_obj;
lean_object* v_a_57_ = stack[1].m_obj;
lean_object* v_a_58_ = stack[2].m_obj;
lean_object* v_a_59_ = stack[3].m_obj;
lean_object* v_a_60_ = stack[4].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_MVarId_ensureNoMVar(v_mvarId_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_ensureNoMVar___boxed(lean_object* v_mvarId_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_MVarId_ensureNoMVar(v_mvarId_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_93_;
}
}
static lean_object* _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_instMonadEIO___redArg();
return v___x_94_;
}
}
lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_toApplicative_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_168_; 
v___x_105_ = lean_obj_once(&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0, &l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0);
v___x_106_ = l_StateRefT_x27_instMonad___redArg(v___x_105_);
v_toApplicative_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v___x_106_, 1);
lean_dec(v_unused_169_);
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_168_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_toApplicative_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_168_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_toFunctor_111_; lean_object* v_toSeq_112_; lean_object* v_toSeqLeft_113_; lean_object* v_toSeqRight_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_166_; 
v_toFunctor_111_ = lean_ctor_get(v_toApplicative_107_, 0);
v_toSeq_112_ = lean_ctor_get(v_toApplicative_107_, 2);
v_toSeqLeft_113_ = lean_ctor_get(v_toApplicative_107_, 3);
v_toSeqRight_114_ = lean_ctor_get(v_toApplicative_107_, 4);
v_isSharedCheck_166_ = !lean_is_exclusive(v_toApplicative_107_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v_toApplicative_107_, 1);
lean_dec(v_unused_167_);
v___x_116_ = v_toApplicative_107_;
v_isShared_117_ = v_isSharedCheck_166_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_toSeqRight_114_);
lean_inc(v_toSeqLeft_113_);
lean_inc(v_toSeq_112_);
lean_inc(v_toFunctor_111_);
lean_dec(v_toApplicative_107_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_166_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___f_125_; lean_object* v___x_127_; 
v___f_118_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1));
v___f_119_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_111_);
v___f_120_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_120_, 0, v_toFunctor_111_);
v___f_121_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_121_, 0, v_toFunctor_111_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___f_120_);
lean_ctor_set(v___x_122_, 1, v___f_121_);
v___f_123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_123_, 0, v_toSeqRight_114_);
v___f_124_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_124_, 0, v_toSeqLeft_113_);
v___f_125_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_125_, 0, v_toSeq_112_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 4, v___f_123_);
lean_ctor_set(v___x_116_, 3, v___f_124_);
lean_ctor_set(v___x_116_, 2, v___f_125_);
lean_ctor_set(v___x_116_, 1, v___f_118_);
lean_ctor_set(v___x_116_, 0, v___x_122_);
v___x_127_ = v___x_116_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___f_118_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v___f_125_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v___f_124_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v___f_123_);
v___x_127_ = v_reuseFailAlloc_165_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___f_119_);
lean_ctor_set(v___x_109_, 0, v___x_127_);
v___x_129_ = v___x_109_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___f_119_);
v___x_129_ = v_reuseFailAlloc_164_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v_toApplicative_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_162_; 
v___x_130_ = l_StateRefT_x27_instMonad___redArg(v___x_129_);
v_toApplicative_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v___x_130_, 1);
lean_dec(v_unused_163_);
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_162_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_toApplicative_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_162_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_toFunctor_135_; lean_object* v_toSeq_136_; lean_object* v_toSeqLeft_137_; lean_object* v_toSeqRight_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_160_; 
v_toFunctor_135_ = lean_ctor_get(v_toApplicative_131_, 0);
v_toSeq_136_ = lean_ctor_get(v_toApplicative_131_, 2);
v_toSeqLeft_137_ = lean_ctor_get(v_toApplicative_131_, 3);
v_toSeqRight_138_ = lean_ctor_get(v_toApplicative_131_, 4);
v_isSharedCheck_160_ = !lean_is_exclusive(v_toApplicative_131_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_toApplicative_131_, 1);
lean_dec(v_unused_161_);
v___x_140_ = v_toApplicative_131_;
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_toSeqRight_138_);
lean_inc(v_toSeqLeft_137_);
lean_inc(v_toSeq_136_);
lean_inc(v_toFunctor_135_);
lean_dec(v_toApplicative_131_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_151_; 
v___f_142_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3));
v___f_143_ = ((lean_object*)(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_135_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_144_, 0, v_toFunctor_135_);
v___f_145_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_145_, 0, v_toFunctor_135_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___f_144_);
lean_ctor_set(v___x_146_, 1, v___f_145_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_147_, 0, v_toSeqRight_138_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_148_, 0, v_toSeqLeft_137_);
v___f_149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_149_, 0, v_toSeq_136_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 4, v___f_147_);
lean_ctor_set(v___x_140_, 3, v___f_148_);
lean_ctor_set(v___x_140_, 2, v___f_149_);
lean_ctor_set(v___x_140_, 1, v___f_142_);
lean_ctor_set(v___x_140_, 0, v___x_146_);
v___x_151_ = v___x_140_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___f_142_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v___f_149_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v___f_148_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v___f_147_);
v___x_151_ = v_reuseFailAlloc_159_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___f_143_);
lean_ctor_set(v___x_133_, 0, v___x_151_);
v___x_153_ = v___x_133_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___f_143_);
v___x_153_ = v_reuseFailAlloc_158_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_1369__overap_156_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_instInhabitedLocalContext_default;
v___x_155_ = l_instInhabitedOfMonad___redArg(v___x_153_, v___x_154_);
v___x_1369__overap_156_ = lean_panic_fn_borrowed(v___x_155_, v_msg_99_);
lean_dec(v___x_155_);
lean_inc(v___y_103_);
lean_inc_ref(v___y_102_);
lean_inc(v___y_101_);
lean_inc_ref(v___y_100_);
v___x_157_ = lean_apply_5(v___x_1369__overap_156_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, lean_box(0));
return v___x_157_;
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
LEAN_EXPORT void l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_99_ = stack[0].m_obj;
lean_object* v___y_100_ = stack[1].m_obj;
lean_object* v___y_101_ = stack[2].m_obj;
lean_object* v___y_102_ = stack[3].m_obj;
lean_object* v___y_103_ = stack[4].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v_msg_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(lean_object* v_t_178_, lean_object* v_k_179_){
_start:
{
if (lean_obj_tag(v_t_178_) == 0)
{
lean_object* v_k_180_; lean_object* v_v_181_; lean_object* v_l_182_; lean_object* v_r_183_; uint8_t v___x_184_; 
v_k_180_ = lean_ctor_get(v_t_178_, 1);
v_v_181_ = lean_ctor_get(v_t_178_, 2);
v_l_182_ = lean_ctor_get(v_t_178_, 3);
v_r_183_ = lean_ctor_get(v_t_178_, 4);
v___x_184_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_179_, v_k_180_);
switch(v___x_184_)
{
case 0:
{
v_t_178_ = v_l_182_;
goto _start;
}
case 1:
{
lean_object* v___x_186_; 
lean_inc(v_v_181_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_v_181_);
return v___x_186_;
}
default: 
{
v_t_178_ = v_r_183_;
goto _start;
}
}
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg___boxed(lean_object* v_t_189_, lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_189_, v_k_190_);
lean_dec(v_k_190_);
lean_dec(v_t_189_);
return v_res_191_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(lean_object* v_auxDeclToFullName_196_, lean_object* v_as_197_, size_t v_i_198_, size_t v_stop_199_, lean_object* v_b_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_a_207_; uint8_t v___x_211_; 
v___x_211_ = lean_usize_dec_eq(v_i_198_, v_stop_199_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_array_uget_borrowed(v_as_197_, v_i_198_);
if (lean_obj_tag(v___x_212_) == 0)
{
v_a_207_ = v_b_200_;
goto v___jp_206_;
}
else
{
lean_object* v_val_213_; 
v_val_213_ = lean_ctor_get(v___x_212_, 0);
if (lean_obj_tag(v_val_213_) == 0)
{
uint8_t v_kind_214_; 
v_kind_214_ = lean_ctor_get_uint8(v_val_213_, sizeof(void*)*4 + 1);
if (v_kind_214_ == 2)
{
lean_object* v_fvarId_215_; lean_object* v_userName_216_; lean_object* v_type_217_; lean_object* v___x_218_; 
v_fvarId_215_ = lean_ctor_get(v_val_213_, 1);
v_userName_216_ = lean_ctor_get(v_val_213_, 2);
v_type_217_ = lean_ctor_get(v_val_213_, 3);
lean_inc_ref(v_type_217_);
v___x_218_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_217_, v___y_202_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_auxDeclToFullName_196_, v_fvarId_215_);
if (lean_obj_tag(v___x_220_) == 1)
{
lean_object* v_val_221_; lean_object* v___x_222_; 
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_220_, 1);
lean_inc(v_userName_216_);
lean_inc(v_fvarId_215_);
v___x_222_ = l_Lean_LocalContext_mkAuxDecl(v_b_200_, v_fvarId_215_, v_userName_216_, v_a_219_, v_val_221_);
v_a_207_ = v___x_222_;
goto v___jp_206_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v___x_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_b_200_);
v___x_223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0));
v___x_224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1));
v___x_225_ = lean_unsigned_to_nat(674u);
v___x_226_ = lean_unsigned_to_nat(12u);
v___x_227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2));
v___x_228_ = 1;
lean_inc(v_userName_216_);
v___x_229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_216_, v___x_228_);
v___x_230_ = lean_string_append(v___x_227_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
v___x_233_ = l_mkPanicMessageWithDecl(v___x_223_, v___x_224_, v___x_225_, v___x_226_, v___x_232_);
lean_dec_ref(v___x_232_);
v___x_234_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v___x_233_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v_a_207_ = v_a_235_;
goto v___jp_206_;
}
else
{
return v___x_234_;
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec_ref(v_b_200_);
v_a_236_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_218_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_218_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_fvarId_244_; lean_object* v_userName_245_; lean_object* v_type_246_; uint8_t v_bi_247_; lean_object* v___x_248_; 
v_fvarId_244_ = lean_ctor_get(v_val_213_, 1);
v_userName_245_ = lean_ctor_get(v_val_213_, 2);
v_type_246_ = lean_ctor_get(v_val_213_, 3);
v_bi_247_ = lean_ctor_get_uint8(v_val_213_, sizeof(void*)*4);
lean_inc_ref(v_type_246_);
v___x_248_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_246_, v___y_202_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
lean_inc(v_userName_245_);
lean_inc(v_fvarId_244_);
v___x_250_ = l_Lean_LocalContext_mkLocalDecl(v_b_200_, v_fvarId_244_, v_userName_245_, v_a_249_, v_bi_247_, v_kind_214_);
v_a_207_ = v___x_250_;
goto v___jp_206_;
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v_b_200_);
v_a_251_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_248_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_248_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
else
{
lean_object* v_fvarId_259_; lean_object* v_userName_260_; lean_object* v_type_261_; lean_object* v_value_262_; uint8_t v_nondep_263_; uint8_t v_kind_264_; lean_object* v___x_265_; 
v_fvarId_259_ = lean_ctor_get(v_val_213_, 1);
v_userName_260_ = lean_ctor_get(v_val_213_, 2);
v_type_261_ = lean_ctor_get(v_val_213_, 3);
v_value_262_ = lean_ctor_get(v_val_213_, 4);
v_nondep_263_ = lean_ctor_get_uint8(v_val_213_, sizeof(void*)*5);
v_kind_264_ = lean_ctor_get_uint8(v_val_213_, sizeof(void*)*5 + 1);
lean_inc_ref(v_type_261_);
v___x_265_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_261_, v___y_202_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
lean_inc_ref(v_value_262_);
v___x_267_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_value_262_, v___y_202_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
lean_inc(v_userName_260_);
lean_inc(v_fvarId_259_);
v___x_269_ = l_Lean_LocalContext_mkLetDecl(v_b_200_, v_fvarId_259_, v_userName_260_, v_a_266_, v_a_268_, v_nondep_263_, v_kind_264_);
v_a_207_ = v___x_269_;
goto v___jp_206_;
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_266_);
lean_dec_ref(v_b_200_);
v_a_270_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_267_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_267_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_b_200_);
v_a_278_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_265_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_265_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_b_200_);
return v___x_286_;
}
v___jp_206_:
{
size_t v___x_208_; size_t v___x_209_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_198_, v___x_208_);
v_i_198_ = v___x_209_;
v_b_200_ = v_a_207_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_196_ = stack[0].m_obj;
lean_object* v_as_197_ = stack[1].m_obj;
size_t v_i_198_ = stack[2].m_num;
size_t v_stop_199_ = stack[3].m_num;
lean_object* v_b_200_ = stack[4].m_obj;
lean_object* v___y_201_ = stack[5].m_obj;
lean_object* v___y_202_ = stack[6].m_obj;
lean_object* v___y_203_ = stack[7].m_obj;
lean_object* v___y_204_ = stack[8].m_obj;
lean_object* v_res_287_;
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_196_, v_as_197_, v_i_198_, v_stop_199_, v_b_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___boxed(lean_object* v_auxDeclToFullName_288_, lean_object* v_as_289_, lean_object* v_i_290_, lean_object* v_stop_291_, lean_object* v_b_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
size_t v_i_boxed_298_; size_t v_stop_boxed_299_; lean_object* v_res_300_; 
v_i_boxed_298_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_stop_boxed_299_ = lean_unbox_usize(v_stop_291_);
lean_dec(v_stop_291_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_288_, v_as_289_, v_i_boxed_298_, v_stop_boxed_299_, v_b_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec_ref(v_as_289_);
lean_dec(v_auxDeclToFullName_288_);
return v_res_300_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(lean_object* v_auxDeclToFullName_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v_cs_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_322_; 
v_cs_309_ = lean_ctor_get(v_x_302_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_322_ == 0)
{
v___x_311_ = v_x_302_;
v_isShared_312_ = v_isSharedCheck_322_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_cs_309_);
lean_dec(v_x_302_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_322_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v_cs_309_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_317_; 
lean_dec_ref(v_cs_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v_x_303_);
v___x_317_ = v___x_311_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_x_303_);
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
lean_del_object(v___x_311_);
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_314_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_301_, v_cs_309_, v___x_319_, v___x_320_, v_x_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec_ref(v_cs_309_);
return v___x_321_;
}
}
}
else
{
lean_object* v_vs_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_336_; 
v_vs_323_ = lean_ctor_get(v_x_302_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_336_ == 0)
{
v___x_325_ = v_x_302_;
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_vs_323_);
lean_dec(v_x_302_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get_size(v_vs_323_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_vs_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 0);
lean_ctor_set(v___x_325_, 0, v_x_303_);
v___x_331_ = v___x_325_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_x_303_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
lean_del_object(v___x_325_);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_328_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_301_, v_vs_323_, v___x_333_, v___x_334_, v_x_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec_ref(v_vs_323_);
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_301_ = stack[0].m_obj;
lean_object* v_x_302_ = stack[1].m_obj;
lean_object* v_x_303_ = stack[2].m_obj;
lean_object* v___y_304_ = stack[3].m_obj;
lean_object* v___y_305_ = stack[4].m_obj;
lean_object* v___y_306_ = stack[5].m_obj;
lean_object* v___y_307_ = stack[6].m_obj;
lean_object* v_res_337_;
v_res_337_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_301_, v_x_302_, v_x_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
stack->m_obj
 = v_res_337_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_338_, lean_object* v_as_339_, size_t v_i_340_, size_t v_stop_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = lean_usize_dec_eq(v_i_340_, v_stop_341_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_array_uget_borrowed(v_as_339_, v_i_340_);
lean_inc(v___x_349_);
v___x_350_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_338_, v___x_349_, v_b_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; size_t v___x_352_; size_t v___x_353_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_add(v_i_340_, v___x_352_);
v_i_340_ = v___x_353_;
v_b_342_ = v_a_351_;
goto _start;
}
else
{
return v___x_350_;
}
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_b_342_);
return v___x_355_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_338_ = stack[0].m_obj;
lean_object* v_as_339_ = stack[1].m_obj;
size_t v_i_340_ = stack[2].m_num;
size_t v_stop_341_ = stack[3].m_num;
lean_object* v_b_342_ = stack[4].m_obj;
lean_object* v___y_343_ = stack[5].m_obj;
lean_object* v___y_344_ = stack[6].m_obj;
lean_object* v___y_345_ = stack[7].m_obj;
lean_object* v___y_346_ = stack[8].m_obj;
lean_object* v_res_356_;
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_338_, v_as_339_, v_i_340_, v_stop_341_, v_b_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_357_, lean_object* v_as_358_, lean_object* v_i_359_, lean_object* v_stop_360_, lean_object* v_b_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
size_t v_i_boxed_367_; size_t v_stop_boxed_368_; lean_object* v_res_369_; 
v_i_boxed_367_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_stop_boxed_368_ = lean_unbox_usize(v_stop_360_);
lean_dec(v_stop_360_);
v_res_369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_357_, v_as_358_, v_i_boxed_367_, v_stop_boxed_368_, v_b_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v_as_358_);
lean_dec(v_auxDeclToFullName_357_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_auxDeclToFullName_370_, lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_370_, v_x_371_, v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v_auxDeclToFullName_370_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_379_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(lean_object* v_auxDeclToFullName_380_, lean_object* v_x_381_, size_t v_x_382_, size_t v_x_383_, lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v_cs_390_; lean_object* v___x_391_; size_t v___x_392_; lean_object* v_j_393_; lean_object* v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_cs_390_ = lean_ctor_get(v_x_381_, 0);
lean_inc_ref(v_cs_390_);
lean_dec_ref_known(v_x_381_, 1);
v___x_391_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0);
v___x_392_ = lean_usize_shift_right(v_x_382_, v_x_383_);
v_j_393_ = lean_usize_to_nat(v___x_392_);
v___x_394_ = lean_array_get_borrowed(v___x_391_, v_cs_390_, v_j_393_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_shift_left(v___x_395_, v_x_383_);
v___x_397_ = lean_usize_sub(v___x_396_, v___x_395_);
v___x_398_ = lean_usize_land(v_x_382_, v___x_397_);
v___x_399_ = ((size_t)5ULL);
v___x_400_ = lean_usize_sub(v_x_383_, v___x_399_);
lean_inc(v___x_394_);
v___x_401_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_380_, v___x_394_, v___x_398_, v___x_400_, v_x_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_j_393_, v___x_403_);
lean_dec(v_j_393_);
v___x_405_ = lean_array_get_size(v_cs_390_);
v___x_406_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec(v___x_404_);
lean_dec_ref(v_cs_390_);
return v___x_401_;
}
else
{
size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; 
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_407_ = lean_usize_of_nat(v___x_404_);
lean_dec(v___x_404_);
v___x_408_ = lean_usize_of_nat(v___x_405_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_380_, v_cs_390_, v___x_407_, v___x_408_, v_a_402_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec_ref(v_cs_390_);
return v___x_409_;
}
}
else
{
lean_dec(v_j_393_);
lean_dec_ref(v_cs_390_);
return v___x_401_;
}
}
else
{
lean_object* v_vs_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_423_; 
v_vs_410_ = lean_ctor_get(v_x_381_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_423_ == 0)
{
v___x_412_ = v_x_381_;
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_vs_410_);
lean_dec(v_x_381_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_usize_to_nat(v_x_382_);
v___x_415_ = lean_array_get_size(v_vs_410_);
v___x_416_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_418_; 
lean_dec(v___x_414_);
lean_dec_ref(v_vs_410_);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 0);
lean_ctor_set(v___x_412_, 0, v_x_384_);
v___x_418_ = v___x_412_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_x_384_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
lean_del_object(v___x_412_);
v___x_420_ = lean_usize_of_nat(v___x_414_);
lean_dec(v___x_414_);
v___x_421_ = lean_usize_of_nat(v___x_415_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_380_, v_vs_410_, v___x_420_, v___x_421_, v_x_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec_ref(v_vs_410_);
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_380_ = stack[0].m_obj;
lean_object* v_x_381_ = stack[1].m_obj;
size_t v_x_382_ = stack[2].m_num;
size_t v_x_383_ = stack[3].m_num;
lean_object* v_x_384_ = stack[4].m_obj;
lean_object* v___y_385_ = stack[5].m_obj;
lean_object* v___y_386_ = stack[6].m_obj;
lean_object* v___y_387_ = stack[7].m_obj;
lean_object* v___y_388_ = stack[8].m_obj;
lean_object* v_res_424_;
v_res_424_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_380_, v_x_381_, v_x_382_, v_x_383_, v_x_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
size_t v_x_4297__boxed_435_; size_t v_x_4298__boxed_436_; lean_object* v_res_437_; 
v_x_4297__boxed_435_ = lean_unbox_usize(v_x_427_);
lean_dec(v_x_427_);
v_x_4298__boxed_436_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_437_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_425_, v_x_426_, v_x_4297__boxed_435_, v_x_4298__boxed_436_, v_x_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v_auxDeclToFullName_425_);
return v_res_437_;
}
}
lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(lean_object* v_auxDeclToFullName_438_, lean_object* v_t_439_, lean_object* v_init_440_, lean_object* v_start_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_nat_dec_eq(v_start_441_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v_root_449_; lean_object* v_tail_450_; size_t v_shift_451_; lean_object* v_tailOff_452_; uint8_t v___x_453_; 
v_root_449_ = lean_ctor_get(v_t_439_, 0);
lean_inc_ref(v_root_449_);
v_tail_450_ = lean_ctor_get(v_t_439_, 1);
lean_inc_ref(v_tail_450_);
v_shift_451_ = lean_ctor_get_usize(v_t_439_, 4);
v_tailOff_452_ = lean_ctor_get(v_t_439_, 3);
lean_inc(v_tailOff_452_);
lean_dec_ref(v_t_439_);
v___x_453_ = lean_nat_dec_le(v_tailOff_452_, v_start_441_);
if (v___x_453_ == 0)
{
size_t v___x_454_; lean_object* v___x_455_; 
lean_dec(v_tailOff_452_);
v___x_454_ = lean_usize_of_nat(v_start_441_);
v___x_455_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_438_, v_root_449_, v___x_454_, v_shift_451_, v_init_440_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v___x_457_ = lean_array_get_size(v_tail_450_);
v___x_458_ = lean_nat_dec_lt(v___x_447_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec_ref(v_tail_450_);
return v___x_455_;
}
else
{
size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_459_ = ((size_t)0ULL);
v___x_460_ = lean_usize_of_nat(v___x_457_);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_438_, v_tail_450_, v___x_459_, v___x_460_, v_a_456_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_450_);
return v___x_461_;
}
}
else
{
lean_dec_ref(v_tail_450_);
return v___x_455_;
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
lean_dec_ref(v_root_449_);
v___x_462_ = lean_nat_sub(v_start_441_, v_tailOff_452_);
lean_dec(v_tailOff_452_);
v___x_463_ = lean_array_get_size(v_tail_450_);
v___x_464_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec(v___x_462_);
lean_dec_ref(v_tail_450_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_init_440_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_usize_of_nat(v___x_462_);
lean_dec(v___x_462_);
v___x_467_ = lean_usize_of_nat(v___x_463_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_438_, v_tail_450_, v___x_466_, v___x_467_, v_init_440_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_450_);
return v___x_468_;
}
}
}
else
{
lean_object* v_root_469_; lean_object* v_tail_470_; lean_object* v___x_471_; 
v_root_469_ = lean_ctor_get(v_t_439_, 0);
lean_inc_ref(v_root_469_);
v_tail_470_ = lean_ctor_get(v_t_439_, 1);
lean_inc_ref(v_tail_470_);
lean_dec_ref(v_t_439_);
v___x_471_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_438_, v_root_469_, v_init_440_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v___x_473_ = lean_array_get_size(v_tail_470_);
v___x_474_ = lean_nat_dec_lt(v___x_447_, v___x_473_);
if (v___x_474_ == 0)
{
lean_dec_ref(v_tail_470_);
return v___x_471_;
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_475_ = ((size_t)0ULL);
v___x_476_ = lean_usize_of_nat(v___x_473_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_438_, v_tail_470_, v___x_475_, v___x_476_, v_a_472_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec_ref(v_tail_470_);
return v___x_477_;
}
}
else
{
lean_dec_ref(v_tail_470_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_438_ = stack[0].m_obj;
lean_object* v_t_439_ = stack[1].m_obj;
lean_object* v_init_440_ = stack[2].m_obj;
lean_object* v_start_441_ = stack[3].m_obj;
lean_object* v___y_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v___y_444_ = stack[6].m_obj;
lean_object* v___y_445_ = stack[7].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_438_, v_t_439_, v_init_440_, v_start_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3___boxed(lean_object* v_auxDeclToFullName_479_, lean_object* v_t_480_, lean_object* v_init_481_, lean_object* v_start_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_479_, v_t_480_, v_init_481_, v_start_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v_start_482_);
lean_dec(v_auxDeclToFullName_479_);
return v_res_488_;
}
}
lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(lean_object* v_auxDeclToFullName_489_, lean_object* v_lctx_490_, lean_object* v_init_491_, lean_object* v_start_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_decls_498_; lean_object* v___x_499_; 
v_decls_498_ = lean_ctor_get(v_lctx_490_, 1);
lean_inc_ref(v_decls_498_);
lean_dec_ref(v_lctx_490_);
v___x_499_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_489_, v_decls_498_, v_init_491_, v_start_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_499_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_489_ = stack[0].m_obj;
lean_object* v_lctx_490_ = stack[1].m_obj;
lean_object* v_init_491_ = stack[2].m_obj;
lean_object* v_start_492_ = stack[3].m_obj;
lean_object* v___y_493_ = stack[4].m_obj;
lean_object* v___y_494_ = stack[5].m_obj;
lean_object* v___y_495_ = stack[6].m_obj;
lean_object* v___y_496_ = stack[7].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_489_, v_lctx_490_, v_init_491_, v_start_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2___boxed(lean_object* v_auxDeclToFullName_501_, lean_object* v_lctx_502_, lean_object* v_init_503_, lean_object* v_start_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_501_, v_lctx_502_, v_init_503_, v_start_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v_start_504_);
lean_dec(v_auxDeclToFullName_501_);
return v_res_510_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_511_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_unsigned_to_nat(32u);
v___x_515_ = lean_mk_empty_array_with_capacity(v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3(void){
_start:
{
size_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_517_ = ((size_t)5ULL);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_unsigned_to_nat(32u);
v___x_520_ = lean_mk_empty_array_with_capacity(v___x_519_);
v___x_521_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2);
v___x_522_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
lean_ctor_set(v___x_522_, 2, v___x_518_);
lean_ctor_set(v___x_522_, 3, v___x_518_);
lean_ctor_set_usize(v___x_522_, 4, v___x_517_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_523_ = lean_box(1);
v___x_524_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3);
v___x_525_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1);
v___x_526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
lean_ctor_set(v___x_526_, 2, v___x_523_);
return v___x_526_;
}
}
lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(lean_object* v_lctx_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_auxDeclToFullName_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_auxDeclToFullName_533_ = lean_ctor_get(v_lctx_527_, 2);
lean_inc(v_auxDeclToFullName_533_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4);
v___x_536_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_533_, v_lctx_527_, v___x_535_, v___x_534_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v_auxDeclToFullName_533_);
return v___x_536_;
}
}
LEAN_EXPORT void l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_527_ = stack[0].m_obj;
lean_object* v___y_528_ = stack[1].m_obj;
lean_object* v___y_529_ = stack[2].m_obj;
lean_object* v___y_530_ = stack[3].m_obj;
lean_object* v___y_531_ = stack[4].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___boxed(lean_object* v_lctx_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_574_; 
v_ks_549_ = lean_ctor_get(v_x_545_, 0);
v_vs_550_ = lean_ctor_get(v_x_545_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_574_ == 0)
{
v___x_552_ = v_x_545_;
v_isShared_553_ = v_isSharedCheck_574_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_vs_550_);
lean_inc(v_ks_549_);
lean_dec(v_x_545_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_574_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_size(v_ks_549_);
v___x_555_ = lean_nat_dec_lt(v_x_546_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_x_546_);
v___x_556_ = lean_array_push(v_ks_549_, v_x_547_);
v___x_557_ = lean_array_push(v_vs_550_, v_x_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_557_);
lean_ctor_set(v___x_552_, 0, v___x_556_);
v___x_559_ = v___x_552_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v_k_x27_561_; uint8_t v___x_562_; 
v_k_x27_561_ = lean_array_fget_borrowed(v_ks_549_, v_x_546_);
v___x_562_ = l_Lean_instBEqMVarId_beq(v_x_547_, v_k_x27_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_564_; 
if (v_isShared_553_ == 0)
{
v___x_564_ = v___x_552_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_ks_549_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_vs_550_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_x_546_, v___x_565_);
lean_dec(v_x_546_);
v_x_545_ = v___x_564_;
v_x_546_ = v___x_566_;
goto _start;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = lean_array_fset(v_ks_549_, v_x_546_, v_x_547_);
v___x_570_ = lean_array_fset(v_vs_550_, v_x_546_, v_x_548_);
lean_dec(v_x_546_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_570_);
lean_ctor_set(v___x_552_, 0, v___x_569_);
v___x_572_ = v___x_552_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(lean_object* v_n_575_, lean_object* v_k_576_, lean_object* v_v_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_n_575_, v___x_578_, v_k_576_, v_v_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_580_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(lean_object* v_x_581_, size_t v_x_582_, size_t v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v_es_586_; size_t v___x_587_; size_t v___x_588_; lean_object* v_j_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_es_586_ = lean_ctor_get(v_x_581_, 0);
v___x_587_ = ((size_t)31ULL);
v___x_588_ = lean_usize_land(v_x_582_, v___x_587_);
v_j_589_ = lean_usize_to_nat(v___x_588_);
v___x_590_ = lean_array_get_size(v_es_586_);
v___x_591_ = lean_nat_dec_lt(v_j_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_dec(v_j_589_);
lean_dec(v_x_585_);
lean_dec(v_x_584_);
return v_x_581_;
}
else
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_630_; 
lean_inc_ref(v_es_586_);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_x_581_, 0);
lean_dec(v_unused_631_);
v___x_593_ = v_x_581_;
v_isShared_594_ = v_isSharedCheck_630_;
goto v_resetjp_592_;
}
else
{
lean_dec(v_x_581_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_630_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_v_595_; lean_object* v___x_596_; lean_object* v_xs_x27_597_; lean_object* v___y_599_; 
v_v_595_ = lean_array_fget(v_es_586_, v_j_589_);
v___x_596_ = lean_box(0);
v_xs_x27_597_ = lean_array_fset(v_es_586_, v_j_589_, v___x_596_);
switch(lean_obj_tag(v_v_595_))
{
case 0:
{
lean_object* v_key_604_; lean_object* v_val_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_615_; 
v_key_604_ = lean_ctor_get(v_v_595_, 0);
v_val_605_ = lean_ctor_get(v_v_595_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_v_595_);
if (v_isSharedCheck_615_ == 0)
{
v___x_607_ = v_v_595_;
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_val_605_);
lean_inc(v_key_604_);
lean_dec(v_v_595_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_615_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_instBEqMVarId_beq(v_x_584_, v_key_604_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_607_);
v___x_610_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_604_, v_val_605_, v_x_584_, v_x_585_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
v___y_599_ = v___x_611_;
goto v___jp_598_;
}
else
{
lean_object* v___x_613_; 
lean_dec(v_val_605_);
lean_dec(v_key_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_x_585_);
lean_ctor_set(v___x_607_, 0, v_x_584_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_x_584_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_x_585_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v___y_599_ = v___x_613_;
goto v___jp_598_;
}
}
}
}
case 1:
{
lean_object* v_node_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_node_616_ = lean_ctor_get(v_v_595_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_v_595_);
if (v_isSharedCheck_628_ == 0)
{
v___x_618_ = v_v_595_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_node_616_);
lean_dec(v_v_595_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_620_ = ((size_t)5ULL);
v___x_621_ = lean_usize_shift_right(v_x_582_, v___x_620_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_x_583_, v___x_622_);
v___x_624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_node_616_, v___x_621_, v___x_623_, v_x_584_, v_x_585_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_624_);
v___x_626_ = v___x_618_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
v___y_599_ = v___x_626_;
goto v___jp_598_;
}
}
}
default: 
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_x_584_);
lean_ctor_set(v___x_629_, 1, v_x_585_);
v___y_599_ = v___x_629_;
goto v___jp_598_;
}
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_array_fset(v_xs_x27_597_, v_j_589_, v___y_599_);
lean_dec(v_j_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_600_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
else
{
lean_object* v_ks_632_; lean_object* v_vs_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_651_; 
v_ks_632_ = lean_ctor_get(v_x_581_, 0);
v_vs_633_ = lean_ctor_get(v_x_581_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_651_ == 0)
{
v___x_635_ = v_x_581_;
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_vs_633_);
lean_inc(v_ks_632_);
lean_dec(v_x_581_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_ks_632_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_vs_633_);
v___x_638_ = v_reuseFailAlloc_650_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v_newNode_639_; size_t v___x_640_; uint8_t v___x_641_; 
v_newNode_639_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v___x_638_, v_x_584_, v_x_585_);
v___x_640_ = ((size_t)7ULL);
v___x_641_ = lean_usize_dec_le(v___x_640_, v_x_583_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_639_);
v___x_643_ = lean_unsigned_to_nat(4u);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
lean_dec(v___x_642_);
if (v___x_644_ == 0)
{
lean_object* v_ks_645_; lean_object* v_vs_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_ks_645_ = lean_ctor_get(v_newNode_639_, 0);
lean_inc_ref(v_ks_645_);
v_vs_646_ = lean_ctor_get(v_newNode_639_, 1);
lean_inc_ref(v_vs_646_);
lean_dec_ref(v_newNode_639_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0);
v___x_649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_x_583_, v_ks_645_, v_vs_646_, v___x_647_, v___x_648_);
lean_dec_ref(v_vs_646_);
lean_dec_ref(v_ks_645_);
return v___x_649_;
}
else
{
return v_newNode_639_;
}
}
else
{
return v_newNode_639_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_581_ = stack[0].m_obj;
size_t v_x_582_ = stack[1].m_num;
size_t v_x_583_ = stack[2].m_num;
lean_object* v_x_584_ = stack[3].m_obj;
lean_object* v_x_585_ = stack[4].m_obj;
lean_object* v_res_652_;
v_res_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_581_, v_x_582_, v_x_583_, v_x_584_, v_x_585_);
stack->m_obj
 = v_res_652_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(size_t v_depth_653_, lean_object* v_keys_654_, lean_object* v_vals_655_, lean_object* v_i_656_, lean_object* v_entries_657_){
_start:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_array_get_size(v_keys_654_);
v___x_659_ = lean_nat_dec_lt(v_i_656_, v___x_658_);
if (v___x_659_ == 0)
{
lean_dec(v_i_656_);
return v_entries_657_;
}
else
{
lean_object* v_k_660_; lean_object* v_v_661_; uint64_t v___x_662_; size_t v_h_663_; size_t v___x_664_; lean_object* v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v_h_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_k_660_ = lean_array_fget_borrowed(v_keys_654_, v_i_656_);
v_v_661_ = lean_array_fget_borrowed(v_vals_655_, v_i_656_);
v___x_662_ = l_Lean_instHashableMVarId_hash(v_k_660_);
v_h_663_ = lean_uint64_to_usize(v___x_662_);
v___x_664_ = ((size_t)5ULL);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_sub(v_depth_653_, v___x_666_);
v___x_668_ = lean_usize_mul(v___x_664_, v___x_667_);
v_h_669_ = lean_usize_shift_right(v_h_663_, v___x_668_);
v___x_670_ = lean_nat_add(v_i_656_, v___x_665_);
lean_dec(v_i_656_);
lean_inc(v_v_661_);
lean_inc(v_k_660_);
v___x_671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_entries_657_, v_h_669_, v_depth_653_, v_k_660_, v_v_661_);
v_i_656_ = v___x_670_;
v_entries_657_ = v___x_671_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_653_ = stack[0].m_num;
lean_object* v_keys_654_ = stack[1].m_obj;
lean_object* v_vals_655_ = stack[2].m_obj;
lean_object* v_i_656_ = stack[3].m_obj;
lean_object* v_entries_657_ = stack[4].m_obj;
lean_object* v_res_673_;
v_res_673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_653_, v_keys_654_, v_vals_655_, v_i_656_, v_entries_657_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg___boxed(lean_object* v_depth_674_, lean_object* v_keys_675_, lean_object* v_vals_676_, lean_object* v_i_677_, lean_object* v_entries_678_){
_start:
{
size_t v_depth_boxed_679_; lean_object* v_res_680_; 
v_depth_boxed_679_ = lean_unbox_usize(v_depth_674_);
lean_dec(v_depth_674_);
v_res_680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_boxed_679_, v_keys_675_, v_vals_676_, v_i_677_, v_entries_678_);
lean_dec_ref(v_vals_676_);
lean_dec_ref(v_keys_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
size_t v_x_4781__boxed_686_; size_t v_x_4782__boxed_687_; lean_object* v_res_688_; 
v_x_4781__boxed_686_ = lean_unbox_usize(v_x_682_);
lean_dec(v_x_682_);
v_x_4782__boxed_687_ = lean_unbox_usize(v_x_683_);
lean_dec(v_x_683_);
v_res_688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_681_, v_x_4781__boxed_686_, v_x_4782__boxed_687_, v_x_684_, v_x_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
uint64_t v___x_692_; size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_692_ = l_Lean_instHashableMVarId_hash(v_x_690_);
v___x_693_ = lean_uint64_to_usize(v___x_692_);
v___x_694_ = ((size_t)1ULL);
v___x_695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_689_, v___x_693_, v___x_694_, v_x_690_, v_x_691_);
return v___x_695_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(lean_object* v_mvarId_696_, lean_object* v_val_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; lean_object* v_mctx_701_; lean_object* v_cache_702_; lean_object* v_zetaDeltaFVarIds_703_; lean_object* v_postponed_704_; lean_object* v_diag_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_735_; 
v___x_700_ = lean_st_ref_take(v___y_698_);
v_mctx_701_ = lean_ctor_get(v___x_700_, 0);
v_cache_702_ = lean_ctor_get(v___x_700_, 1);
v_zetaDeltaFVarIds_703_ = lean_ctor_get(v___x_700_, 2);
v_postponed_704_ = lean_ctor_get(v___x_700_, 3);
v_diag_705_ = lean_ctor_get(v___x_700_, 4);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_735_ == 0)
{
v___x_707_ = v___x_700_;
v_isShared_708_ = v_isSharedCheck_735_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_diag_705_);
lean_inc(v_postponed_704_);
lean_inc(v_zetaDeltaFVarIds_703_);
lean_inc(v_cache_702_);
lean_inc(v_mctx_701_);
lean_dec(v___x_700_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_735_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_depth_709_; lean_object* v_levelAssignDepth_710_; lean_object* v_lmvarCounter_711_; lean_object* v_mvarCounter_712_; lean_object* v_lDecls_713_; lean_object* v_decls_714_; lean_object* v_userNames_715_; lean_object* v_lAssignment_716_; lean_object* v_eAssignment_717_; lean_object* v_dAssignment_718_; lean_object* v_instanceTypedMVars_719_; lean_object* v_synthNormMemo_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_734_; 
v_depth_709_ = lean_ctor_get(v_mctx_701_, 0);
v_levelAssignDepth_710_ = lean_ctor_get(v_mctx_701_, 1);
v_lmvarCounter_711_ = lean_ctor_get(v_mctx_701_, 2);
v_mvarCounter_712_ = lean_ctor_get(v_mctx_701_, 3);
v_lDecls_713_ = lean_ctor_get(v_mctx_701_, 4);
v_decls_714_ = lean_ctor_get(v_mctx_701_, 5);
v_userNames_715_ = lean_ctor_get(v_mctx_701_, 6);
v_lAssignment_716_ = lean_ctor_get(v_mctx_701_, 7);
v_eAssignment_717_ = lean_ctor_get(v_mctx_701_, 8);
v_dAssignment_718_ = lean_ctor_get(v_mctx_701_, 9);
v_instanceTypedMVars_719_ = lean_ctor_get(v_mctx_701_, 10);
v_synthNormMemo_720_ = lean_ctor_get(v_mctx_701_, 11);
v_isSharedCheck_734_ = !lean_is_exclusive(v_mctx_701_);
if (v_isSharedCheck_734_ == 0)
{
v___x_722_ = v_mctx_701_;
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_synthNormMemo_720_);
lean_inc(v_instanceTypedMVars_719_);
lean_inc(v_dAssignment_718_);
lean_inc(v_eAssignment_717_);
lean_inc(v_lAssignment_716_);
lean_inc(v_userNames_715_);
lean_inc(v_decls_714_);
lean_inc(v_lDecls_713_);
lean_inc(v_mvarCounter_712_);
lean_inc(v_lmvarCounter_711_);
lean_inc(v_levelAssignDepth_710_);
lean_inc(v_depth_709_);
lean_dec(v_mctx_701_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = lean_box(0);
v___x_725_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_717_, v_mvarId_696_, v_val_697_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 8, v___x_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_depth_709_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_levelAssignDepth_710_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_lmvarCounter_711_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_mvarCounter_712_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_lDecls_713_);
lean_ctor_set(v_reuseFailAlloc_733_, 5, v_decls_714_);
lean_ctor_set(v_reuseFailAlloc_733_, 6, v_userNames_715_);
lean_ctor_set(v_reuseFailAlloc_733_, 7, v_lAssignment_716_);
lean_ctor_set(v_reuseFailAlloc_733_, 8, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_733_, 9, v_dAssignment_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 10, v_instanceTypedMVars_719_);
lean_ctor_set(v_reuseFailAlloc_733_, 11, v_synthNormMemo_720_);
v___x_727_ = v_reuseFailAlloc_733_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_727_);
v___x_729_ = v___x_707_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_cache_702_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_zetaDeltaFVarIds_703_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_postponed_704_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_diag_705_);
v___x_729_ = v_reuseFailAlloc_732_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_st_ref_put(v___y_698_, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_724_);
return v___x_731_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_696_ = stack[0].m_obj;
lean_object* v_val_697_ = stack[1].m_obj;
lean_object* v___y_698_ = stack[2].m_obj;
lean_object* v_res_736_;
v_res_736_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_696_, v_val_697_, v___y_698_);
stack->m_obj
 = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(lean_object* v_mvarId_737_, lean_object* v_val_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_737_, v_val_738_, v___y_739_);
lean_dec(v___y_739_);
return v_res_741_;
}
}
lean_object* l_Lean_MVarId_instantiateGoalMVars(lean_object* v_mvarId_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_742_);
v___x_749_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_742_, v___x_748_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v___x_750_; 
lean_dec_ref_known(v___x_749_, 1);
lean_inc(v_mvarId_742_);
v___x_750_ = l_Lean_MVarId_getDecl(v_mvarId_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_userName_752_; lean_object* v_lctx_753_; lean_object* v_type_754_; lean_object* v_localInstances_755_; lean_object* v___x_756_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v_userName_752_ = lean_ctor_get(v_a_751_, 0);
lean_inc(v_userName_752_);
v_lctx_753_ = lean_ctor_get(v_a_751_, 1);
lean_inc_ref(v_lctx_753_);
v_type_754_ = lean_ctor_get(v_a_751_, 2);
lean_inc_ref(v_type_754_);
v_localInstances_755_ = lean_ctor_get(v_a_751_, 4);
lean_inc_ref(v_localInstances_755_);
lean_dec(v_a_751_);
v___x_756_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_753_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v_a_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v___x_758_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_754_, v_a_744_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_758_);
v___x_760_ = 2;
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_757_, v_localInstances_755_, v_a_759_, v___x_760_, v_userName_752_, v___x_761_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_772_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc_n(v_a_763_, 2);
lean_dec_ref_known(v___x_762_, 1);
v___x_764_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_742_, v_a_763_, v_a_744_);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v___x_764_, 0);
lean_dec(v_unused_773_);
v___x_766_ = v___x_764_;
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
else
{
lean_dec(v___x_764_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = l_Lean_Expr_mvarId_x21(v_a_763_);
lean_dec(v_a_763_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_mvarId_742_);
v_a_774_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_762_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_762_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec_ref(v_localInstances_755_);
lean_dec_ref(v_type_754_);
lean_dec(v_userName_752_);
lean_dec(v_mvarId_742_);
v_a_782_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_756_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_756_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_mvarId_742_);
v_a_790_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_750_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_750_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_mvarId_742_);
v_a_798_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_749_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_749_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_instantiateGoalMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_742_ = stack[0].m_obj;
lean_object* v_a_743_ = stack[1].m_obj;
lean_object* v_a_744_ = stack[2].m_obj;
lean_object* v_a_745_ = stack[3].m_obj;
lean_object* v_a_746_ = stack[4].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lean_MVarId_instantiateGoalMVars(v_mvarId_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars___boxed(lean_object* v_mvarId_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_MVarId_instantiateGoalMVars(v_mvarId_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_813_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(lean_object* v_mvarId_814_, lean_object* v_val_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_814_, v_val_815_, v___y_817_);
return v___x_821_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_814_ = stack[0].m_obj;
lean_object* v_val_815_ = stack[1].m_obj;
lean_object* v___y_816_ = stack[2].m_obj;
lean_object* v___y_817_ = stack[3].m_obj;
lean_object* v___y_818_ = stack[4].m_obj;
lean_object* v___y_819_ = stack[5].m_obj;
lean_object* v_res_822_;
v_res_822_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(v_mvarId_814_, v_val_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
stack->m_obj
 = v_res_822_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(lean_object* v_mvarId_823_, lean_object* v_val_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(v_mvarId_823_, v_val_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(lean_object* v_00_u03b4_831_, lean_object* v_t_832_, lean_object* v_k_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_832_, v_k_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b4_835_, lean_object* v_t_836_, lean_object* v_k_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(v_00_u03b4_835_, v_t_836_, v_k_837_);
lean_dec(v_k_837_);
lean_dec(v_t_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(lean_object* v_00_u03b2_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_x_840_, v_x_841_, v_x_842_);
return v___x_843_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_844_, lean_object* v_x_845_, size_t v_x_846_, size_t v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_845_, v_x_846_, v_x_847_, v_x_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_845_ = stack[1].m_obj;
size_t v_x_846_ = stack[2].m_num;
size_t v_x_847_ = stack[3].m_num;
lean_object* v_x_848_ = stack[4].m_obj;
lean_object* v_x_849_ = stack[5].m_obj;
lean_object* v_res_851_;
v_res_851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(lean_box(0), v_x_845_, v_x_846_, v_x_847_, v_x_848_, v_x_849_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
size_t v_x_5323__boxed_858_; size_t v_x_5324__boxed_859_; lean_object* v_res_860_; 
v_x_5323__boxed_858_ = lean_unbox_usize(v_x_854_);
lean_dec(v_x_854_);
v_x_5324__boxed_859_ = lean_unbox_usize(v_x_855_);
lean_dec(v_x_855_);
v_res_860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_852_, v_x_853_, v_x_5323__boxed_858_, v_x_5324__boxed_859_, v_x_856_, v_x_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_861_, lean_object* v_n_862_, lean_object* v_k_863_, lean_object* v_v_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v_n_862_, v_k_863_, v_v_864_);
return v___x_865_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_866_, size_t v_depth_867_, lean_object* v_keys_868_, lean_object* v_vals_869_, lean_object* v_heq_870_, lean_object* v_i_871_, lean_object* v_entries_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_867_, v_keys_868_, v_vals_869_, v_i_871_, v_entries_872_);
return v___x_873_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
size_t v_depth_867_ = stack[1].m_num;
lean_object* v_keys_868_ = stack[2].m_obj;
lean_object* v_vals_869_ = stack[3].m_obj;
lean_object* v_i_871_ = stack[5].m_obj;
lean_object* v_entries_872_ = stack[6].m_obj;
lean_object* v_res_874_;
v_res_874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(lean_box(0), v_depth_867_, v_keys_868_, v_vals_869_, lean_box(0), v_i_871_, v_entries_872_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(lean_object* v_00_u03b2_875_, lean_object* v_depth_876_, lean_object* v_keys_877_, lean_object* v_vals_878_, lean_object* v_heq_879_, lean_object* v_i_880_, lean_object* v_entries_881_){
_start:
{
size_t v_depth_boxed_882_; lean_object* v_res_883_; 
v_depth_boxed_882_ = lean_unbox_usize(v_depth_876_);
lean_dec(v_depth_876_);
v_res_883_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(v_00_u03b2_875_, v_depth_boxed_882_, v_keys_877_, v_vals_878_, v_heq_879_, v_i_880_, v_entries_881_);
lean_dec_ref(v_vals_878_);
lean_dec_ref(v_keys_877_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_x_885_, v_x_886_, v_x_887_, v_x_888_);
return v___x_889_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(lean_object* v_k_890_, lean_object* v_b_891_, lean_object* v_c_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
v___x_898_ = lean_apply_7(v_k_890_, v_b_891_, v_c_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, lean_box(0));
return v___x_898_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_890_ = stack[0].m_obj;
lean_object* v_b_891_ = stack[1].m_obj;
lean_object* v_c_892_ = stack[2].m_obj;
lean_object* v___y_893_ = stack[3].m_obj;
lean_object* v___y_894_ = stack[4].m_obj;
lean_object* v___y_895_ = stack[5].m_obj;
lean_object* v___y_896_ = stack[6].m_obj;
lean_object* v_res_899_;
v_res_899_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(v_k_890_, v_b_891_, v_c_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
stack->m_obj
 = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(lean_object* v_k_900_, lean_object* v_b_901_, lean_object* v_c_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(v_k_900_, v_b_901_, v_c_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(lean_object* v_e_909_, lean_object* v_k_910_, uint8_t v_cleanupAnnotations_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___f_917_; uint8_t v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___f_917_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_917_, 0, v_k_910_);
v___x_918_ = 1;
v___x_919_ = 0;
v___x_920_ = lean_box(0);
v___x_921_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_909_, v___x_918_, v___x_919_, v___x_918_, v___x_919_, v___x_920_, v___f_917_, v_cleanupAnnotations_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
v_a_930_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_921_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_921_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_909_ = stack[0].m_obj;
lean_object* v_k_910_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_911_ = stack[2].m_num;
lean_object* v___y_912_ = stack[3].m_obj;
lean_object* v___y_913_ = stack[4].m_obj;
lean_object* v___y_914_ = stack[5].m_obj;
lean_object* v___y_915_ = stack[6].m_obj;
lean_object* v_res_938_;
v_res_938_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_909_, v_k_910_, v_cleanupAnnotations_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_939_, lean_object* v_k_940_, lean_object* v_cleanupAnnotations_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_947_; lean_object* v_res_948_; 
v_cleanupAnnotations_boxed_947_ = lean_unbox(v_cleanupAnnotations_941_);
v_res_948_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_939_, v_k_940_, v_cleanupAnnotations_boxed_947_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_948_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(lean_object* v_00_u03b1_949_, lean_object* v_e_950_, lean_object* v_k_951_, uint8_t v_cleanupAnnotations_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_950_, v_k_951_, v_cleanupAnnotations_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
return v___x_958_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_950_ = stack[1].m_obj;
lean_object* v_k_951_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_952_ = stack[3].m_num;
lean_object* v___y_953_ = stack[4].m_obj;
lean_object* v___y_954_ = stack[5].m_obj;
lean_object* v___y_955_ = stack[6].m_obj;
lean_object* v___y_956_ = stack[7].m_obj;
lean_object* v_res_959_;
v_res_959_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(lean_box(0), v_e_950_, v_k_951_, v_cleanupAnnotations_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
stack->m_obj
 = v_res_959_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___boxed(lean_object* v_00_u03b1_960_, lean_object* v_e_961_, lean_object* v_k_962_, lean_object* v_cleanupAnnotations_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_969_; lean_object* v_res_970_; 
v_cleanupAnnotations_boxed_969_ = lean_unbox(v_cleanupAnnotations_963_);
v_res_970_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(v_00_u03b1_960_, v_e_961_, v_k_962_, v_cleanupAnnotations_boxed_969_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_970_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(lean_object* v_mvarId_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_971_, v_x_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
v_a_987_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_978_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_978_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_971_ = stack[0].m_obj;
lean_object* v_x_972_ = stack[1].m_obj;
lean_object* v___y_973_ = stack[2].m_obj;
lean_object* v___y_974_ = stack[3].m_obj;
lean_object* v___y_975_ = stack[4].m_obj;
lean_object* v___y_976_ = stack[5].m_obj;
lean_object* v_res_995_;
v_res_995_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_971_, v_x_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg___boxed(lean_object* v_mvarId_996_, lean_object* v_x_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_996_, v_x_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(lean_object* v_00_u03b1_1004_, lean_object* v_mvarId_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1005_ = stack[1].m_obj;
lean_object* v_x_1006_ = stack[2].m_obj;
lean_object* v___y_1007_ = stack[3].m_obj;
lean_object* v___y_1008_ = stack[4].m_obj;
lean_object* v___y_1009_ = stack[5].m_obj;
lean_object* v___y_1010_ = stack[6].m_obj;
lean_object* v_res_1013_;
v_res_1013_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(lean_box(0), v_mvarId_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_mvarId_1015_, lean_object* v_x_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(v_00_u03b1_1014_, v_mvarId_1015_, v_x_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1022_;
}
}
lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t v___x_1023_, uint8_t v___x_1024_, lean_object* v_xs_1025_, lean_object* v_body_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = 1;
v___x_1033_ = l_Lean_Meta_mkForallFVars(v_xs_1025_, v_body_1026_, v___x_1023_, v___x_1024_, v___x_1024_, v___x_1032_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT void l_Lean_MVarId_abstractMVars___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1023_ = stack[0].m_num;
uint8_t v___x_1024_ = stack[1].m_num;
lean_object* v_xs_1025_ = stack[2].m_obj;
lean_object* v_body_1026_ = stack[3].m_obj;
lean_object* v___y_1027_ = stack[4].m_obj;
lean_object* v___y_1028_ = stack[5].m_obj;
lean_object* v___y_1029_ = stack[6].m_obj;
lean_object* v___y_1030_ = stack[7].m_obj;
lean_object* v_res_1034_;
v_res_1034_ = l_Lean_MVarId_abstractMVars___lam__0(v___x_1023_, v___x_1024_, v_xs_1025_, v_body_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
stack->m_obj
 = v_res_1034_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_xs_1037_, lean_object* v_body_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v___x_1867__boxed_1044_; uint8_t v___x_1868__boxed_1045_; lean_object* v_res_1046_; 
v___x_1867__boxed_1044_ = lean_unbox(v___x_1035_);
v___x_1868__boxed_1045_ = lean_unbox(v___x_1036_);
v_res_1046_ = l_Lean_MVarId_abstractMVars___lam__0(v___x_1867__boxed_1044_, v___x_1868__boxed_1045_, v_xs_1037_, v_body_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec_ref(v_xs_1037_);
return v_res_1046_;
}
}
lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object* v_a_1047_, uint8_t v___x_1048_, lean_object* v___f_1049_, lean_object* v_mvarId_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_abstractMVars(v_a_1047_, v___x_1048_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v_mvars_1058_; lean_object* v_expr_1059_; lean_object* v___x_1060_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v_mvars_1058_ = lean_ctor_get(v_a_1057_, 1);
lean_inc_ref(v_mvars_1058_);
v_expr_1059_ = lean_ctor_get(v_a_1057_, 2);
lean_inc_ref(v_expr_1059_);
lean_dec(v_a_1057_);
v___x_1060_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_expr_1059_, v___f_1049_, v___x_1048_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
lean_inc(v_mvarId_1050_);
v___x_1062_ = l_Lean_MVarId_getTag(v_mvarId_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1061_, v_a_1063_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_n(v_a_1065_, 2);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = l_Lean_mkAppN(v_a_1065_, v_mvars_1058_);
lean_dec_ref(v_mvars_1058_);
v___x_1067_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1050_, v___x_1066_, v___y_1052_);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1067_, 0);
lean_dec(v_unused_1076_);
v___x_1069_ = v___x_1067_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v___x_1067_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = l_Lean_Expr_mvarId_x21(v_a_1065_);
lean_dec(v_a_1065_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v_mvars_1058_);
lean_dec(v_mvarId_1050_);
v_a_1077_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1064_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1064_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_a_1061_);
lean_dec_ref(v_mvars_1058_);
lean_dec(v_mvarId_1050_);
v_a_1085_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1062_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1062_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref(v_mvars_1058_);
lean_dec(v_mvarId_1050_);
v_a_1093_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1060_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1060_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_mvarId_1050_);
lean_dec_ref(v___f_1049_);
v_a_1101_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1056_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1056_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_abstractMVars___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1047_ = stack[0].m_obj;
uint8_t v___x_1048_ = stack[1].m_num;
lean_object* v___f_1049_ = stack[2].m_obj;
lean_object* v_mvarId_1050_ = stack[3].m_obj;
lean_object* v___y_1051_ = stack[4].m_obj;
lean_object* v___y_1052_ = stack[5].m_obj;
lean_object* v___y_1053_ = stack[6].m_obj;
lean_object* v___y_1054_ = stack[7].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l_Lean_MVarId_abstractMVars___lam__1(v_a_1047_, v___x_1048_, v___f_1049_, v_mvarId_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object* v_a_1110_, lean_object* v___x_1111_, lean_object* v___f_1112_, lean_object* v_mvarId_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v___x_1909__boxed_1119_; lean_object* v_res_1120_; 
v___x_1909__boxed_1119_ = lean_unbox(v___x_1111_);
v_res_1120_ = l_Lean_MVarId_abstractMVars___lam__1(v_a_1110_, v___x_1909__boxed_1119_, v___f_1112_, v_mvarId_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1120_;
}
}
lean_object* l_Lean_MVarId_abstractMVars(lean_object* v_mvarId_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1121_);
v___x_1128_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1121_, v___x_1127_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref_known(v___x_1128_, 1);
lean_inc(v_mvarId_1121_);
v___x_1129_ = l_Lean_MVarId_getType(v_mvarId_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1147_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_1130_, v_a_1123_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1147_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1147_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_Lean_Expr_hasExprMVar(v_a_1132_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v_a_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v_mvarId_1121_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_mvarId_1121_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1134_);
v___x_1140_ = 0;
v___x_1141_ = lean_box(v___x_1140_);
v___x_1142_ = lean_box(v___x_1136_);
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1143_, 0, v___x_1141_);
lean_closure_set(v___f_1143_, 1, v___x_1142_);
v___x_1144_ = lean_box(v___x_1140_);
lean_inc(v_mvarId_1121_);
v___f_1145_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1145_, 0, v_a_1132_);
lean_closure_set(v___f_1145_, 1, v___x_1144_);
lean_closure_set(v___f_1145_, 2, v___f_1143_);
lean_closure_set(v___f_1145_, 3, v_mvarId_1121_);
v___x_1146_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1121_, v___f_1145_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_mvarId_1121_);
v_a_1148_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1129_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1129_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_mvarId_1121_);
v_a_1156_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1128_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1128_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_abstractMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1121_ = stack[0].m_obj;
lean_object* v_a_1122_ = stack[1].m_obj;
lean_object* v_a_1123_ = stack[2].m_obj;
lean_object* v_a_1124_ = stack[3].m_obj;
lean_object* v_a_1125_ = stack[4].m_obj;
lean_object* v_res_1164_;
v_res_1164_ = l_Lean_MVarId_abstractMVars(v_mvarId_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
stack->m_obj
 = v_res_1164_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___boxed(lean_object* v_mvarId_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_MVarId_abstractMVars(v_mvarId_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1171_;
}
}
lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object* v_mvarId_1172_, lean_object* v___x_1173_, lean_object* v_f_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
lean_inc(v_mvarId_1172_);
v___x_1180_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1172_, v___x_1173_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v___x_1181_; 
lean_dec_ref_known(v___x_1180_, 1);
lean_inc(v_mvarId_1172_);
v___x_1181_ = l_Lean_MVarId_getTag(v_mvarId_1172_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
lean_inc(v_mvarId_1172_);
v___x_1183_ = l_Lean_MVarId_getType(v_mvarId_1172_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
lean_inc(v___y_1178_);
lean_inc_ref(v___y_1177_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1185_ = lean_apply_6(v_f_1174_, v_a_1184_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, lean_box(0));
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1186_, v_a_1182_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v___y_1175_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1197_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_n(v_a_1188_, 2);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1172_, v_a_1188_, v___y_1176_);
lean_dec(v___y_1176_);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1189_, 0);
lean_dec(v_unused_1198_);
v___x_1191_ = v___x_1189_;
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v___x_1189_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1197_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = l_Lean_Expr_mvarId_x21(v_a_1188_);
lean_dec(v_a_1188_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1193_);
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v___y_1176_);
lean_dec(v_mvarId_1172_);
v_a_1199_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1187_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1187_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1182_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v_mvarId_1172_);
v_a_1207_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1185_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1185_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_a_1182_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_f_1174_);
lean_dec(v_mvarId_1172_);
v_a_1215_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1183_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1183_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_f_1174_);
lean_dec(v_mvarId_1172_);
v_a_1223_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1181_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1181_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_f_1174_);
lean_dec(v_mvarId_1172_);
v_a_1231_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1180_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1180_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_transformTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1172_ = stack[0].m_obj;
lean_object* v___x_1173_ = stack[1].m_obj;
lean_object* v_f_1174_ = stack[2].m_obj;
lean_object* v___y_1175_ = stack[3].m_obj;
lean_object* v___y_1176_ = stack[4].m_obj;
lean_object* v___y_1177_ = stack[5].m_obj;
lean_object* v___y_1178_ = stack[6].m_obj;
lean_object* v_res_1239_;
v_res_1239_ = l_Lean_MVarId_transformTarget___lam__0(v_mvarId_1172_, v___x_1173_, v_f_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
stack->m_obj
 = v_res_1239_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0___boxed(lean_object* v_mvarId_1240_, lean_object* v___x_1241_, lean_object* v_f_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_MVarId_transformTarget___lam__0(v_mvarId_1240_, v___x_1241_, v_f_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v_res_1248_;
}
}
lean_object* l_Lean_MVarId_transformTarget(lean_object* v_mvarId_1249_, lean_object* v_f_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1249_);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_MVarId_transformTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1257_, 0, v_mvarId_1249_);
lean_closure_set(v___f_1257_, 1, v___x_1256_);
lean_closure_set(v___f_1257_, 2, v_f_1250_);
v___x_1258_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1249_, v___f_1257_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
return v___x_1258_;
}
}
LEAN_EXPORT void l_Lean_MVarId_transformTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1249_ = stack[0].m_obj;
lean_object* v_f_1250_ = stack[1].m_obj;
lean_object* v_a_1251_ = stack[2].m_obj;
lean_object* v_a_1252_ = stack[3].m_obj;
lean_object* v_a_1253_ = stack[4].m_obj;
lean_object* v_a_1254_ = stack[5].m_obj;
lean_object* v_res_1259_;
v_res_1259_ = l_Lean_MVarId_transformTarget(v_mvarId_1249_, v_f_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
stack->m_obj
 = v_res_1259_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___boxed(lean_object* v_mvarId_1260_, lean_object* v_f_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_MVarId_transformTarget(v_mvarId_1260_, v_f_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1267_;
}
}
lean_object* l_Lean_MVarId_unfoldReducible(lean_object* v_mvarId_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_Lean_MVarId_unfoldReducible___closed__0));
v___x_1276_ = l_Lean_MVarId_transformTarget(v_mvarId_1269_, v___x_1275_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
return v___x_1276_;
}
}
LEAN_EXPORT void l_Lean_MVarId_unfoldReducible_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1269_ = stack[0].m_obj;
lean_object* v_a_1270_ = stack[1].m_obj;
lean_object* v_a_1271_ = stack[2].m_obj;
lean_object* v_a_1272_ = stack[3].m_obj;
lean_object* v_a_1273_ = stack[4].m_obj;
lean_object* v_res_1277_;
v_res_1277_ = l_Lean_MVarId_unfoldReducible(v_mvarId_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
stack->m_obj
 = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible___boxed(lean_object* v_mvarId_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_MVarId_unfoldReducible(v_mvarId_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
return v_res_1284_;
}
}
lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object* v_x_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Core_betaReduce(v_x_1285_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT void l_Lean_MVarId_betaReduce___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1285_ = stack[0].m_obj;
lean_object* v___y_1286_ = stack[1].m_obj;
lean_object* v___y_1287_ = stack[2].m_obj;
lean_object* v___y_1288_ = stack[3].m_obj;
lean_object* v___y_1289_ = stack[4].m_obj;
lean_object* v_res_1292_;
v_res_1292_ = l_Lean_MVarId_betaReduce___lam__0(v_x_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
stack->m_obj
 = v_res_1292_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object* v_x_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_MVarId_betaReduce___lam__0(v_x_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1299_;
}
}
lean_object* l_Lean_MVarId_betaReduce(lean_object* v_mvarId_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___f_1307_; lean_object* v___x_1308_; 
v___f_1307_ = ((lean_object*)(l_Lean_MVarId_betaReduce___closed__0));
v___x_1308_ = l_Lean_MVarId_transformTarget(v_mvarId_1301_, v___f_1307_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
return v___x_1308_;
}
}
LEAN_EXPORT void l_Lean_MVarId_betaReduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1301_ = stack[0].m_obj;
lean_object* v_a_1302_ = stack[1].m_obj;
lean_object* v_a_1303_ = stack[2].m_obj;
lean_object* v_a_1304_ = stack[3].m_obj;
lean_object* v_a_1305_ = stack[4].m_obj;
lean_object* v_res_1309_;
v_res_1309_ = l_Lean_MVarId_betaReduce(v_mvarId_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
stack->m_obj
 = v_res_1309_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___boxed(lean_object* v_mvarId_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_MVarId_betaReduce(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
return v_res_1316_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__1));
v___x_1322_ = l_Lean_mkConst(v___x_1321_, v___x_1320_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_box(0);
v___x_1329_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__5));
v___x_1330_ = l_Lean_mkConst(v___x_1329_, v___x_1328_);
return v___x_1330_;
}
}
lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object* v_mvarId_1331_, lean_object* v___x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
lean_inc(v_mvarId_1331_);
v___x_1338_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1331_, v___x_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref_known(v___x_1338_, 1);
lean_inc(v_mvarId_1331_);
v___x_1339_ = l_Lean_MVarId_getType(v_mvarId_1331_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1394_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1394_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1394_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint8_t v___x_1344_; 
lean_inc(v_a_1340_);
v___x_1344_ = l_Lean_Expr_isFalse(v_a_1340_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_del_object(v___x_1342_);
lean_inc(v_a_1340_);
v___x_1345_ = l_Lean_mkNot(v_a_1340_);
v___x_1346_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__2, &l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2);
v___x_1347_ = l_Lean_mkArrow(v___x_1345_, v___x_1346_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
lean_inc(v_mvarId_1331_);
v___x_1349_ = l_Lean_MVarId_getTag(v_mvarId_1331_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1348_, v_a_1350_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1364_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_n(v_a_1352_, 2);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__6, &l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6);
v___x_1354_ = l_Lean_mkAppB(v___x_1353_, v_a_1340_, v_a_1352_);
v___x_1355_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1331_, v___x_1354_, v___y_1334_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v___x_1355_, 0);
lean_dec(v_unused_1365_);
v___x_1357_ = v___x_1355_;
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v___x_1355_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1364_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = l_Lean_Expr_mvarId_x21(v_a_1352_);
lean_dec(v_a_1352_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1340_);
lean_dec(v_mvarId_1331_);
v_a_1366_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1351_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1351_);
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
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1348_);
lean_dec(v_a_1340_);
lean_dec(v_mvarId_1331_);
v_a_1374_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1349_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1349_);
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
lean_dec(v_a_1340_);
lean_dec(v_mvarId_1331_);
v_a_1382_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1347_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1347_);
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
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec(v_a_1340_);
lean_dec(v_mvarId_1331_);
v___x_1390_ = lean_box(0);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1390_);
v___x_1392_ = v___x_1342_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_mvarId_1331_);
v_a_1395_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1339_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1339_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
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
lean_dec(v_mvarId_1331_);
v_a_1403_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1338_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1338_);
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
}
LEAN_EXPORT void l_Lean_MVarId_byContra_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1331_ = stack[0].m_obj;
lean_object* v___x_1332_ = stack[1].m_obj;
lean_object* v___y_1333_ = stack[2].m_obj;
lean_object* v___y_1334_ = stack[3].m_obj;
lean_object* v___y_1335_ = stack[4].m_obj;
lean_object* v___y_1336_ = stack[5].m_obj;
lean_object* v_res_1411_;
v_res_1411_ = l_Lean_MVarId_byContra_x3f___lam__0(v_mvarId_1331_, v___x_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
stack->m_obj
 = v_res_1411_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object* v_mvarId_1412_, lean_object* v___x_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_MVarId_byContra_x3f___lam__0(v_mvarId_1412_, v___x_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1419_;
}
}
lean_object* l_Lean_MVarId_byContra_x3f(lean_object* v_mvarId_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___closed__1));
lean_inc(v_mvarId_1424_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_MVarId_byContra_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1431_, 0, v_mvarId_1424_);
lean_closure_set(v___f_1431_, 1, v___x_1430_);
v___x_1432_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1424_, v___f_1431_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
return v___x_1432_;
}
}
LEAN_EXPORT void l_Lean_MVarId_byContra_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1424_ = stack[0].m_obj;
lean_object* v_a_1425_ = stack[1].m_obj;
lean_object* v_a_1426_ = stack[2].m_obj;
lean_object* v_a_1427_ = stack[3].m_obj;
lean_object* v_a_1428_ = stack[4].m_obj;
lean_object* v_res_1433_;
v_res_1433_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
stack->m_obj
 = v_res_1433_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___boxed(lean_object* v_mvarId_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1440_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0));
v___x_1443_ = l_Lean_stringToMessageData(v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2));
v___x_1446_ = l_Lean_stringToMessageData(v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(lean_object* v_as_x27_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
if (lean_obj_tag(v_as_x27_1450_) == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_b_1451_);
return v___x_1457_;
}
else
{
lean_object* v_head_1458_; lean_object* v_tail_1459_; lean_object* v___x_1460_; 
v_head_1458_ = lean_ctor_get(v_as_x27_1450_, 0);
v_tail_1459_ = lean_ctor_get(v_as_x27_1450_, 1);
lean_inc(v_head_1458_);
lean_inc(v_b_1451_);
v___x_1460_ = l_Lean_MVarId_clear(v_b_1451_, v_head_1458_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; 
lean_dec(v_b_1451_);
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v_as_x27_1450_ = v_tail_1459_;
v_b_1451_ = v_a_1461_;
goto _start;
}
else
{
lean_object* v_a_1463_; uint8_t v___y_1465_; uint8_t v___x_1506_; 
v_a_1463_ = lean_ctor_get(v___x_1460_, 0);
v___x_1506_ = l_Lean_Exception_isInterrupt(v_a_1463_);
if (v___x_1506_ == 0)
{
uint8_t v___x_1507_; 
lean_inc(v_a_1463_);
v___x_1507_ = l_Lean_Exception_isRuntime(v_a_1463_);
v___y_1465_ = v___x_1507_;
goto v___jp_1464_;
}
else
{
v___y_1465_ = v___x_1506_;
goto v___jp_1464_;
}
v___jp_1464_:
{
if (v___y_1465_ == 0)
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1504_; 
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v___x_1460_, 0);
lean_dec(v_unused_1505_);
v___x_1467_ = v___x_1460_;
v_isShared_1468_ = v_isSharedCheck_1504_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v___x_1460_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1504_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; 
lean_inc(v_head_1458_);
v___x_1469_ = l_Lean_FVarId_getDecl___redArg(v_head_1458_, v___y_1452_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; uint8_t v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = l_Lean_LocalDecl_isAuxDecl(v_a_1470_);
if (v___x_1471_ == 0)
{
lean_dec(v_a_1470_);
lean_del_object(v___x_1467_);
v_as_x27_1450_ = v_tail_1459_;
goto _start;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1473_ = l_Lean_LocalDecl_userName(v_a_1470_);
lean_dec(v_a_1470_);
v___x_1474_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_1475_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
v___x_1476_ = l_Lean_MessageData_ofName(v___x_1473_);
lean_inc_ref(v___x_1476_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___x_1476_);
v___x_1481_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1482_);
v___x_1484_ = v___x_1467_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
lean_inc(v_b_1451_);
v___x_1485_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1474_, v_b_1451_, v___x_1484_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref_known(v___x_1485_, 1);
v_as_x27_1450_ = v_tail_1459_;
goto _start;
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_b_1451_);
v_a_1487_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1485_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_del_object(v___x_1467_);
lean_dec(v_b_1451_);
v_a_1496_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1469_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1469_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
else
{
lean_dec(v_b_1451_);
return v___x_1460_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1450_ = stack[0].m_obj;
lean_object* v_b_1451_ = stack[1].m_obj;
lean_object* v___y_1452_ = stack[2].m_obj;
lean_object* v___y_1453_ = stack[3].m_obj;
lean_object* v___y_1454_ = stack[4].m_obj;
lean_object* v___y_1455_ = stack[5].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1450_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(lean_object* v_as_x27_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1509_, v_b_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_as_x27_1509_);
return v_res_1516_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_1517_, size_t v_sz_1518_, size_t v_i_1519_, lean_object* v_b_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1519_, v_sz_1518_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1520_);
return v___x_1523_;
}
else
{
lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1542_; 
v_snd_1524_ = lean_ctor_get(v_b_1520_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_b_1520_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_b_1520_, 0);
lean_dec(v_unused_1543_);
v___x_1526_ = v_b_1520_;
v_isShared_1527_ = v_isSharedCheck_1542_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_dec(v_b_1520_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1542_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v_a_1530_; lean_object* v_a_1537_; 
v___x_1528_ = lean_box(0);
v_a_1537_ = lean_array_uget_borrowed(v_as_1517_, v_i_1519_);
if (lean_obj_tag(v_a_1537_) == 0)
{
v_a_1530_ = v_snd_1524_;
goto v___jp_1529_;
}
else
{
lean_object* v_val_1538_; uint8_t v___x_1539_; 
v_val_1538_ = lean_ctor_get(v_a_1537_, 0);
v___x_1539_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1538_);
if (v___x_1539_ == 0)
{
v_a_1530_ = v_snd_1524_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = l_Lean_LocalDecl_fvarId(v_val_1538_);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_snd_1524_);
v_a_1530_ = v___x_1541_;
goto v___jp_1529_;
}
}
v___jp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v_a_1530_);
lean_ctor_set(v___x_1526_, 0, v___x_1528_);
v___x_1532_ = v___x_1526_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_a_1530_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
size_t v___x_1533_; size_t v___x_1534_; 
v___x_1533_ = ((size_t)1ULL);
v___x_1534_ = lean_usize_add(v_i_1519_, v___x_1533_);
v_i_1519_ = v___x_1534_;
v_b_1520_ = v___x_1532_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1517_ = stack[0].m_obj;
size_t v_sz_1518_ = stack[1].m_num;
size_t v_i_1519_ = stack[2].m_num;
lean_object* v_b_1520_ = stack[3].m_obj;
lean_object* v_res_1544_;
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1517_, v_sz_1518_, v_i_1519_, v_b_1520_);
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_1545_, lean_object* v_sz_1546_, lean_object* v_i_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_){
_start:
{
size_t v_sz_boxed_1550_; size_t v_i_boxed_1551_; lean_object* v_res_1552_; 
v_sz_boxed_1550_ = lean_unbox_usize(v_sz_1546_);
lean_dec(v_sz_1546_);
v_i_boxed_1551_ = lean_unbox_usize(v_i_1547_);
lean_dec(v_i_1547_);
v_res_1552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1545_, v_sz_boxed_1550_, v_i_boxed_1551_, v_b_1548_);
lean_dec_ref(v_as_1545_);
return v_res_1552_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(lean_object* v_as_1553_, size_t v_sz_1554_, size_t v_i_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_usize_dec_lt(v_i_1555_, v_sz_1554_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_b_1556_);
return v___x_1563_;
}
else
{
lean_object* v_snd_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1582_; 
v_snd_1564_ = lean_ctor_get(v_b_1556_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_b_1556_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_b_1556_, 0);
lean_dec(v_unused_1583_);
v___x_1566_ = v_b_1556_;
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_snd_1564_);
lean_dec(v_b_1556_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v_a_1570_; lean_object* v_a_1577_; 
v___x_1568_ = lean_box(0);
v_a_1577_ = lean_array_uget_borrowed(v_as_1553_, v_i_1555_);
if (lean_obj_tag(v_a_1577_) == 0)
{
v_a_1570_ = v_snd_1564_;
goto v___jp_1569_;
}
else
{
lean_object* v_val_1578_; uint8_t v___x_1579_; 
v_val_1578_ = lean_ctor_get(v_a_1577_, 0);
v___x_1579_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1578_);
if (v___x_1579_ == 0)
{
v_a_1570_ = v_snd_1564_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = l_Lean_LocalDecl_fvarId(v_val_1578_);
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v_snd_1564_);
v_a_1570_ = v___x_1581_;
goto v___jp_1569_;
}
}
v___jp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v_a_1570_);
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1572_ = v___x_1566_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_a_1570_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = ((size_t)1ULL);
v___x_1574_ = lean_usize_add(v_i_1555_, v___x_1573_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1553_, v_sz_1554_, v___x_1574_, v___x_1572_);
return v___x_1575_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1553_ = stack[0].m_obj;
size_t v_sz_1554_ = stack[1].m_num;
size_t v_i_1555_ = stack[2].m_num;
lean_object* v_b_1556_ = stack[3].m_obj;
lean_object* v___y_1557_ = stack[4].m_obj;
lean_object* v___y_1558_ = stack[5].m_obj;
lean_object* v___y_1559_ = stack[6].m_obj;
lean_object* v___y_1560_ = stack[7].m_obj;
lean_object* v_res_1584_;
v_res_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_1553_, v_sz_1554_, v_i_1555_, v_b_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
stack->m_obj
 = v_res_1584_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1585_, lean_object* v_sz_1586_, lean_object* v_i_1587_, lean_object* v_b_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
size_t v_sz_boxed_1594_; size_t v_i_boxed_1595_; lean_object* v_res_1596_; 
v_sz_boxed_1594_ = lean_unbox_usize(v_sz_1586_);
lean_dec(v_sz_1586_);
v_i_boxed_1595_ = lean_unbox_usize(v_i_1587_);
lean_dec(v_i_1587_);
v_res_1596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_1585_, v_sz_boxed_1594_, v_i_boxed_1595_, v_b_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v_as_1585_);
return v_res_1596_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object* v_init_1597_, lean_object* v_n_1598_, lean_object* v_b_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
if (lean_obj_tag(v_n_1598_) == 0)
{
lean_object* v_cs_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; size_t v_sz_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v_cs_1605_ = lean_ctor_get(v_n_1598_, 0);
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v_b_1599_);
v_sz_1608_ = lean_array_size(v_cs_1605_);
v___x_1609_ = ((size_t)0ULL);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1597_, v_cs_1605_, v_sz_1608_, v___x_1609_, v___x_1607_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1625_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1625_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1625_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_fst_1615_; 
v_fst_1615_ = lean_ctor_get(v_a_1611_, 0);
if (lean_obj_tag(v_fst_1615_) == 0)
{
lean_object* v_snd_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v_snd_1616_ = lean_ctor_get(v_a_1611_, 1);
lean_inc(v_snd_1616_);
lean_dec(v_a_1611_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_snd_1616_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1617_);
v___x_1619_ = v___x_1613_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_object* v_val_1621_; lean_object* v___x_1623_; 
lean_inc_ref(v_fst_1615_);
lean_dec(v_a_1611_);
v_val_1621_ = lean_ctor_get(v_fst_1615_, 0);
lean_inc(v_val_1621_);
lean_dec_ref_known(v_fst_1615_, 1);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_val_1621_);
v___x_1623_ = v___x_1613_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_val_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1610_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1610_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_object* v_vs_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; size_t v_sz_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
v_vs_1634_ = lean_ctor_get(v_n_1598_, 0);
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v_b_1599_);
v_sz_1637_ = lean_array_size(v_vs_1634_);
v___x_1638_ = ((size_t)0ULL);
v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_1634_, v_sz_1637_, v___x_1638_, v___x_1636_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1654_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_fst_1644_; 
v_fst_1644_ = lean_ctor_get(v_a_1640_, 0);
if (lean_obj_tag(v_fst_1644_) == 0)
{
lean_object* v_snd_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v_snd_1645_ = lean_ctor_get(v_a_1640_, 1);
lean_inc(v_snd_1645_);
lean_dec(v_a_1640_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_snd_1645_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1646_);
v___x_1648_ = v___x_1642_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
else
{
lean_object* v_val_1650_; lean_object* v___x_1652_; 
lean_inc_ref(v_fst_1644_);
lean_dec(v_a_1640_);
v_val_1650_ = lean_ctor_get(v_fst_1644_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v_fst_1644_, 1);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v_val_1650_);
v___x_1652_ = v___x_1642_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_val_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_a_1655_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1639_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1639_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1597_ = stack[0].m_obj;
lean_object* v_n_1598_ = stack[1].m_obj;
lean_object* v_b_1599_ = stack[2].m_obj;
lean_object* v___y_1600_ = stack[3].m_obj;
lean_object* v___y_1601_ = stack[4].m_obj;
lean_object* v___y_1602_ = stack[5].m_obj;
lean_object* v___y_1603_ = stack[6].m_obj;
lean_object* v_res_1663_;
v_res_1663_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1597_, v_n_1598_, v_b_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
stack->m_obj
 = v_res_1663_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object* v_init_1664_, lean_object* v_as_1665_, size_t v_sz_1666_, size_t v_i_1667_, lean_object* v_b_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_usize_dec_lt(v_i_1667_, v_sz_1666_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v_b_1668_);
return v___x_1675_;
}
else
{
lean_object* v_snd_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1710_; 
v_snd_1676_ = lean_ctor_get(v_b_1668_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_b_1668_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v_b_1668_, 0);
lean_dec(v_unused_1711_);
v___x_1678_ = v_b_1668_;
v_isShared_1679_ = v_isSharedCheck_1710_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_snd_1676_);
lean_dec(v_b_1668_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1710_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_box(0);
v_a_1681_ = lean_array_uget_borrowed(v_as_1665_, v_i_1667_);
lean_inc(v_snd_1676_);
v___x_1682_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1664_, v_a_1681_, v_snd_1676_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1701_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1701_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1701_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
if (lean_obj_tag(v_a_1683_) == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_a_1683_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1687_);
v___x_1689_ = v___x_1678_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_snd_1676_);
v___x_1689_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1689_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; 
lean_del_object(v___x_1685_);
lean_dec(v_snd_1676_);
v_a_1694_ = lean_ctor_get(v_a_1683_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v_a_1683_, 1);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v_a_1694_);
lean_ctor_set(v___x_1678_, 0, v___x_1680_);
v___x_1696_ = v___x_1678_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_a_1694_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
size_t v___x_1697_; size_t v___x_1698_; 
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_add(v_i_1667_, v___x_1697_);
v_i_1667_ = v___x_1698_;
v_b_1668_ = v___x_1696_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_del_object(v___x_1678_);
lean_dec(v_snd_1676_);
v_a_1702_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1682_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1682_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1664_ = stack[0].m_obj;
lean_object* v_as_1665_ = stack[1].m_obj;
size_t v_sz_1666_ = stack[2].m_num;
size_t v_i_1667_ = stack[3].m_num;
lean_object* v_b_1668_ = stack[4].m_obj;
lean_object* v___y_1669_ = stack[5].m_obj;
lean_object* v___y_1670_ = stack[6].m_obj;
lean_object* v___y_1671_ = stack[7].m_obj;
lean_object* v___y_1672_ = stack[8].m_obj;
lean_object* v_res_1712_;
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1664_, v_as_1665_, v_sz_1666_, v_i_1667_, v_b_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
stack->m_obj
 = v_res_1712_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1713_, lean_object* v_as_1714_, lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_b_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1713_, v_as_1714_, v_sz_boxed_1723_, v_i_boxed_1724_, v_b_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec_ref(v_as_1714_);
lean_dec(v_init_1713_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object* v_init_1726_, lean_object* v_n_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1726_, v_n_1727_, v_b_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec_ref(v_n_1727_);
lean_dec(v_init_1726_);
return v_res_1734_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1735_, size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_b_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_b_1738_);
return v___x_1741_;
}
else
{
lean_object* v_snd_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1760_; 
v_snd_1742_ = lean_ctor_get(v_b_1738_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_b_1738_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_b_1738_, 0);
lean_dec(v_unused_1761_);
v___x_1744_ = v_b_1738_;
v_isShared_1745_ = v_isSharedCheck_1760_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snd_1742_);
lean_dec(v_b_1738_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1760_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v_a_1748_; lean_object* v_a_1755_; 
v___x_1746_ = lean_box(0);
v_a_1755_ = lean_array_uget_borrowed(v_as_1735_, v_i_1737_);
if (lean_obj_tag(v_a_1755_) == 0)
{
v_a_1748_ = v_snd_1742_;
goto v___jp_1747_;
}
else
{
lean_object* v_val_1756_; uint8_t v___x_1757_; 
v_val_1756_ = lean_ctor_get(v_a_1755_, 0);
v___x_1757_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1756_);
if (v___x_1757_ == 0)
{
v_a_1748_ = v_snd_1742_;
goto v___jp_1747_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = l_Lean_LocalDecl_fvarId(v_val_1756_);
v___x_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v_snd_1742_);
v_a_1748_ = v___x_1759_;
goto v___jp_1747_;
}
}
v___jp_1747_:
{
lean_object* v___x_1750_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_a_1748_);
lean_ctor_set(v___x_1744_, 0, v___x_1746_);
v___x_1750_ = v___x_1744_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_a_1748_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
size_t v___x_1751_; size_t v___x_1752_; 
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1737_, v___x_1751_);
v_i_1737_ = v___x_1752_;
v_b_1738_ = v___x_1750_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1735_ = stack[0].m_obj;
size_t v_sz_1736_ = stack[1].m_num;
size_t v_i_1737_ = stack[2].m_num;
lean_object* v_b_1738_ = stack[3].m_obj;
lean_object* v_res_1762_;
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1735_, v_sz_1736_, v_i_1737_, v_b_1738_);
stack->m_obj
 = v_res_1762_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(lean_object* v_as_1771_, size_t v_sz_1772_, size_t v_i_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1771_ = stack[0].m_obj;
size_t v_sz_1772_ = stack[1].m_num;
size_t v_i_1773_ = stack[2].m_num;
lean_object* v_b_1774_ = stack[3].m_obj;
lean_object* v___y_1775_ = stack[4].m_obj;
lean_object* v___y_1776_ = stack[5].m_obj;
lean_object* v___y_1777_ = stack[6].m_obj;
lean_object* v___y_1778_ = stack[7].m_obj;
lean_object* v_res_1802_;
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_1771_, v_sz_1772_, v_i_1773_, v_b_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
stack->m_obj
 = v_res_1802_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(lean_object* v_as_1803_, lean_object* v_sz_1804_, lean_object* v_i_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
size_t v_sz_boxed_1812_; size_t v_i_boxed_1813_; lean_object* v_res_1814_; 
v_sz_boxed_1812_ = lean_unbox_usize(v_sz_1804_);
lean_dec(v_sz_1804_);
v_i_boxed_1813_ = lean_unbox_usize(v_i_1805_);
lean_dec(v_i_1805_);
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_1803_, v_sz_boxed_1812_, v_i_boxed_1813_, v_b_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_as_1803_);
return v_res_1814_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(lean_object* v_t_1815_, lean_object* v_init_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_root_1822_; lean_object* v_tail_1823_; lean_object* v___x_1824_; 
v_root_1822_ = lean_ctor_get(v_t_1815_, 0);
v_tail_1823_ = lean_ctor_get(v_t_1815_, 1);
lean_inc(v_init_1816_);
v___x_1824_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1816_, v_root_1822_, v_init_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v_init_1816_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1861_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1861_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1861_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
if (lean_obj_tag(v_a_1825_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; 
v_a_1829_ = lean_ctor_get(v_a_1825_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v_a_1825_, 1);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v_a_1829_);
v___x_1831_ = v___x_1827_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; size_t v_sz_1836_; size_t v___x_1837_; lean_object* v___x_1838_; 
lean_del_object(v___x_1827_);
v_a_1833_ = lean_ctor_get(v_a_1825_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v_a_1825_, 1);
v___x_1834_ = lean_box(0);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v_a_1833_);
v_sz_1836_ = lean_array_size(v_tail_1823_);
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_1823_, v_sz_1836_, v___x_1837_, v___x_1835_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1852_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1852_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1852_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_fst_1843_; 
v_fst_1843_ = lean_ctor_get(v_a_1839_, 0);
if (lean_obj_tag(v_fst_1843_) == 0)
{
lean_object* v_snd_1844_; lean_object* v___x_1846_; 
v_snd_1844_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1844_);
lean_dec(v_a_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_snd_1844_);
v___x_1846_ = v___x_1841_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_snd_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
else
{
lean_object* v_val_1848_; lean_object* v___x_1850_; 
lean_inc_ref(v_fst_1843_);
lean_dec(v_a_1839_);
v_val_1848_ = lean_ctor_get(v_fst_1843_, 0);
lean_inc(v_val_1848_);
lean_dec_ref_known(v_fst_1843_, 1);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_val_1848_);
v___x_1850_ = v___x_1841_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_val_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_a_1853_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1838_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1838_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1824_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1824_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1815_ = stack[0].m_obj;
lean_object* v_init_1816_ = stack[1].m_obj;
lean_object* v___y_1817_ = stack[2].m_obj;
lean_object* v___y_1818_ = stack[3].m_obj;
lean_object* v___y_1819_ = stack[4].m_obj;
lean_object* v___y_1820_ = stack[5].m_obj;
lean_object* v_res_1870_;
v_res_1870_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_t_1815_, v_init_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
stack->m_obj
 = v_res_1870_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(lean_object* v_t_1871_, lean_object* v_init_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_t_1871_, v_init_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v_t_1871_);
return v_res_1878_;
}
}
lean_object* l_Lean_MVarId_clearImplDetails___lam__0(lean_object* v_mvarId_1879_, lean_object* v___x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
lean_inc(v_mvarId_1879_);
v___x_1886_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1879_, v___x_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_lctx_1887_; lean_object* v_decls_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec_ref_known(v___x_1886_, 1);
v_lctx_1887_ = lean_ctor_get(v___y_1881_, 2);
v_decls_1888_ = lean_ctor_get(v_lctx_1887_, 1);
v___x_1889_ = lean_box(0);
v___x_1890_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_decls_1888_, v___x_1889_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1900_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
uint8_t v___x_1895_; 
v___x_1895_ = l_List_isEmpty___redArg(v_a_1891_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_del_object(v___x_1893_);
v___x_1896_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_a_1891_, v_mvarId_1879_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v_a_1891_);
return v___x_1896_;
}
else
{
lean_object* v___x_1898_; 
lean_dec(v_a_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_mvarId_1879_);
v___x_1898_ = v___x_1893_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_mvarId_1879_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_mvarId_1879_);
v_a_1901_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1890_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1890_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_mvarId_1879_);
v_a_1909_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1886_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1886_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_clearImplDetails___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1879_ = stack[0].m_obj;
lean_object* v___x_1880_ = stack[1].m_obj;
lean_object* v___y_1881_ = stack[2].m_obj;
lean_object* v___y_1882_ = stack[3].m_obj;
lean_object* v___y_1883_ = stack[4].m_obj;
lean_object* v___y_1884_ = stack[5].m_obj;
lean_object* v_res_1917_;
v_res_1917_ = l_Lean_MVarId_clearImplDetails___lam__0(v_mvarId_1879_, v___x_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
stack->m_obj
 = v_res_1917_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0___boxed(lean_object* v_mvarId_1918_, lean_object* v___x_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_MVarId_clearImplDetails___lam__0(v_mvarId_1918_, v___x_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1925_;
}
}
lean_object* l_Lean_MVarId_clearImplDetails(lean_object* v_mvarId_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; 
v___x_1936_ = ((lean_object*)(l_Lean_MVarId_clearImplDetails___closed__1));
lean_inc(v_mvarId_1930_);
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearImplDetails___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1937_, 0, v_mvarId_1930_);
lean_closure_set(v___f_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1930_, v___f_1937_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT void l_Lean_MVarId_clearImplDetails_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1930_ = stack[0].m_obj;
lean_object* v_a_1931_ = stack[1].m_obj;
lean_object* v_a_1932_ = stack[2].m_obj;
lean_object* v_a_1933_ = stack[3].m_obj;
lean_object* v_a_1934_ = stack[4].m_obj;
lean_object* v_res_1939_;
v_res_1939_ = l_Lean_MVarId_clearImplDetails(v_mvarId_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
stack->m_obj
 = v_res_1939_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___boxed(lean_object* v_mvarId_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_MVarId_clearImplDetails(v_mvarId_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
return v_res_1946_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(lean_object* v_as_1947_, lean_object* v_as_x27_1948_, lean_object* v_b_1949_, lean_object* v_a_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1948_, v_b_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1947_ = stack[0].m_obj;
lean_object* v_as_x27_1948_ = stack[1].m_obj;
lean_object* v_b_1949_ = stack[2].m_obj;
lean_object* v___y_1951_ = stack[4].m_obj;
lean_object* v___y_1952_ = stack[5].m_obj;
lean_object* v___y_1953_ = stack[6].m_obj;
lean_object* v___y_1954_ = stack[7].m_obj;
lean_object* v_res_1957_;
v_res_1957_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(v_as_1947_, v_as_x27_1948_, v_b_1949_, lean_box(0), v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
stack->m_obj
 = v_res_1957_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___boxed(lean_object* v_as_1958_, lean_object* v_as_x27_1959_, lean_object* v_b_1960_, lean_object* v_a_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(v_as_1958_, v_as_x27_1959_, v_b_1960_, v_a_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_as_x27_1959_);
lean_dec(v_as_1958_);
return v_res_1967_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(lean_object* v_as_1968_, size_t v_sz_1969_, size_t v_i_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1968_, v_sz_1969_, v_i_1970_, v_b_1971_);
return v___x_1977_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1968_ = stack[0].m_obj;
size_t v_sz_1969_ = stack[1].m_num;
size_t v_i_1970_ = stack[2].m_num;
lean_object* v_b_1971_ = stack[3].m_obj;
lean_object* v___y_1972_ = stack[4].m_obj;
lean_object* v___y_1973_ = stack[5].m_obj;
lean_object* v___y_1974_ = stack[6].m_obj;
lean_object* v___y_1975_ = stack[7].m_obj;
lean_object* v_res_1978_;
v_res_1978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_1968_, v_sz_1969_, v_i_1970_, v_b_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
stack->m_obj
 = v_res_1978_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1979_, lean_object* v_sz_1980_, lean_object* v_i_1981_, lean_object* v_b_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
size_t v_sz_boxed_1988_; size_t v_i_boxed_1989_; lean_object* v_res_1990_; 
v_sz_boxed_1988_ = lean_unbox_usize(v_sz_1980_);
lean_dec(v_sz_1980_);
v_i_boxed_1989_ = lean_unbox_usize(v_i_1981_);
lean_dec(v_i_1981_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_1979_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v_as_1979_);
return v_res_1990_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1991_, size_t v_sz_1992_, size_t v_i_1993_, lean_object* v_b_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1991_, v_sz_1992_, v_i_1993_, v_b_1994_);
return v___x_2000_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1991_ = stack[0].m_obj;
size_t v_sz_1992_ = stack[1].m_num;
size_t v_i_1993_ = stack[2].m_num;
lean_object* v_b_1994_ = stack[3].m_obj;
lean_object* v___y_1995_ = stack[4].m_obj;
lean_object* v___y_1996_ = stack[5].m_obj;
lean_object* v___y_1997_ = stack[6].m_obj;
lean_object* v___y_1998_ = stack[7].m_obj;
lean_object* v_res_2001_;
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_1991_, v_sz_1992_, v_i_1993_, v_b_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
stack->m_obj
 = v_res_2001_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_2002_, lean_object* v_sz_2003_, lean_object* v_i_2004_, lean_object* v_b_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
size_t v_sz_boxed_2011_; size_t v_i_boxed_2012_; lean_object* v_res_2013_; 
v_sz_boxed_2011_ = lean_unbox_usize(v_sz_2003_);
lean_dec(v_sz_2003_);
v_i_boxed_2012_ = lean_unbox_usize(v_i_2004_);
lean_dec(v_i_2004_);
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_2002_, v_sz_boxed_2011_, v_i_boxed_2012_, v_b_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec_ref(v_as_2002_);
return v_res_2013_;
}
}
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object* v_e_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
switch(lean_obj_tag(v_e_2014_))
{
case 8:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_e_2014_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
case 6:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_e_2014_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
case 10:
{
lean_object* v_expr_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_expr_2022_ = lean_ctor_get(v_e_2014_, 1);
lean_inc_ref(v_expr_2022_);
lean_dec_ref_known(v_e_2014_, 2);
v___x_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_expr_2022_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
default: 
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_e_2014_);
v___x_2026_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2014_ = stack[0].m_obj;
lean_object* v___y_2015_ = stack[1].m_obj;
lean_object* v___y_2016_ = stack[2].m_obj;
lean_object* v_res_2028_;
v_res_2028_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_2014_, v___y_2015_, v___y_2016_);
stack->m_obj
 = v_res_2028_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object* v_e_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v_res_2033_;
}
}
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object* v_e_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_e_2034_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2034_ = stack[0].m_obj;
lean_object* v___y_2035_ = stack[1].m_obj;
lean_object* v___y_2036_ = stack[2].m_obj;
lean_object* v_res_2040_;
v_res_2040_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_2034_, v___y_2035_, v___y_2036_);
stack->m_obj
 = v_res_2040_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object* v_e_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2045_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_object* v_00_u03b1_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_apply_1(v_x_2047_, lean_box(0));
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2047_ = stack[1].m_obj;
lean_object* v___y_2048_ = stack[2].m_obj;
lean_object* v___y_2049_ = stack[3].m_obj;
lean_object* v_res_2053_;
v_res_2053_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v_x_2047_, v___y_2048_, v___y_2049_);
stack->m_obj
 = v_res_2053_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(v_00_u03b1_2054_, v_x_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_2060_, lean_object* v_x_2061_){
_start:
{
if (lean_obj_tag(v_x_2061_) == 0)
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_box(0);
return v___x_2062_;
}
else
{
lean_object* v_key_2063_; lean_object* v_value_2064_; lean_object* v_tail_2065_; uint8_t v___x_2066_; 
v_key_2063_ = lean_ctor_get(v_x_2061_, 0);
v_value_2064_ = lean_ctor_get(v_x_2061_, 1);
v_tail_2065_ = lean_ctor_get(v_x_2061_, 2);
v___x_2066_ = l_Lean_ExprStructEq_beq(v_key_2063_, v_a_2060_);
if (v___x_2066_ == 0)
{
v_x_2061_ = v_tail_2065_;
goto _start;
}
else
{
lean_object* v___x_2068_; 
lean_inc(v_value_2064_);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_value_2064_);
return v___x_2068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2069_, v_x_2070_);
lean_dec(v_x_2070_);
lean_dec_ref(v_a_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_buckets_2074_; lean_object* v___x_2075_; uint64_t v___x_2076_; uint64_t v___x_2077_; uint64_t v___x_2078_; uint64_t v_fold_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; uint64_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_buckets_2074_ = lean_ctor_get(v_m_2072_, 1);
v___x_2075_ = lean_array_get_size(v_buckets_2074_);
v___x_2076_ = l_Lean_ExprStructEq_hash(v_a_2073_);
v___x_2077_ = 32ULL;
v___x_2078_ = lean_uint64_shift_right(v___x_2076_, v___x_2077_);
v_fold_2079_ = lean_uint64_xor(v___x_2076_, v___x_2078_);
v___x_2080_ = 16ULL;
v___x_2081_ = lean_uint64_shift_right(v_fold_2079_, v___x_2080_);
v___x_2082_ = lean_uint64_xor(v_fold_2079_, v___x_2081_);
v___x_2083_ = lean_uint64_to_usize(v___x_2082_);
v___x_2084_ = lean_usize_of_nat(v___x_2075_);
v___x_2085_ = ((size_t)1ULL);
v___x_2086_ = lean_usize_sub(v___x_2084_, v___x_2085_);
v___x_2087_ = lean_usize_land(v___x_2083_, v___x_2086_);
v___x_2088_ = lean_array_uget_borrowed(v_buckets_2074_, v___x_2087_);
v___x_2089_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2073_, v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2090_, v_a_2091_);
lean_dec_ref(v_a_2091_);
lean_dec_ref(v_m_2090_);
return v_res_2092_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2093_, lean_object* v_x_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_apply_1(v_x_2094_, lean_box(0));
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2094_ = stack[1].m_obj;
lean_object* v___y_2095_ = stack[2].m_obj;
lean_object* v___y_2096_ = stack[3].m_obj;
lean_object* v_res_2100_;
v_res_2100_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v_x_2094_, v___y_2095_, v___y_2096_);
stack->m_obj
 = v_res_2100_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2101_, lean_object* v_x_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_2101_, v_x_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2106_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_box(0);
v___x_2108_ = l_Lean_interruptExceptionId;
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2107_);
return v___x_2109_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2113_;
v_res_2113_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
stack->m_obj
 = v_res_2113_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_2115_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = l_Lean_maxRecDepthErrorMessage;
v___x_2122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_2124_ = l_Lean_MessageData_ofFormat(v___x_2123_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_2126_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_2127_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
return v___x_2127_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_ref_2128_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2128_ = stack[0].m_obj;
lean_object* v_res_2133_;
v_res_2133_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2128_);
stack->m_obj
 = v_res_2133_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2134_);
return v_res_2136_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object* v_x_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___y_2143_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; uint8_t v___y_2156_; uint8_t v___y_2157_; uint16_t v___y_2158_; lean_object* v_toCold_2163_; lean_object* v_currRecDepth_2164_; lean_object* v_ref_2165_; uint16_t v_optionFlags_2166_; uint8_t v_suppressElabErrors_2167_; uint8_t v_isRecordingDeps_2168_; lean_object* v_maxRecDepth_2169_; lean_object* v_cancelTk_x3f_2170_; 
v_toCold_2163_ = lean_ctor_get(v___y_2139_, 0);
v_currRecDepth_2164_ = lean_ctor_get(v___y_2139_, 1);
v_ref_2165_ = lean_ctor_get(v___y_2139_, 2);
v_optionFlags_2166_ = lean_ctor_get_uint16(v___y_2139_, sizeof(void*)*3);
v_suppressElabErrors_2167_ = lean_ctor_get_uint8(v___y_2139_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2168_ = lean_ctor_get_uint8(v___y_2139_, sizeof(void*)*3 + 3);
v_maxRecDepth_2169_ = lean_ctor_get(v_toCold_2163_, 3);
v_cancelTk_x3f_2170_ = lean_ctor_get(v_toCold_2163_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2170_) == 1)
{
lean_object* v_val_2176_; uint8_t v___x_2177_; 
v_val_2176_ = lean_ctor_get(v_cancelTk_x3f_2170_, 0);
v___x_2177_ = l_IO_CancelToken_isSet(v_val_2176_);
if (v___x_2177_ == 0)
{
goto v___jp_2171_;
}
else
{
lean_object* v___x_2178_; lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v_x_2137_);
v___x_2178_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
goto v___jp_2171_;
}
v___jp_2142_:
{
if (lean_obj_tag(v___y_2143_) == 0)
{
return v___y_2143_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_a_2144_ = lean_ctor_get(v___y_2143_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___y_2143_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___y_2143_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___y_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
v___jp_2152_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2159_ = lean_unsigned_to_nat(1u);
v___x_2160_ = lean_nat_add(v___y_2155_, v___x_2159_);
lean_inc_ref(v___y_2154_);
v___x_2161_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2161_, 0, v___y_2154_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
lean_ctor_set(v___x_2161_, 2, v___y_2153_);
lean_ctor_set_uint16(v___x_2161_, sizeof(void*)*3, v___y_2158_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*3 + 2, v___y_2157_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*3 + 3, v___y_2156_);
lean_inc(v___y_2140_);
lean_inc(v___y_2138_);
v___x_2162_ = lean_apply_4(v_x_2137_, v___y_2138_, v___x_2161_, v___y_2140_, lean_box(0));
v___y_2143_ = v___x_2162_;
goto v___jp_2142_;
}
v___jp_2171_:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = lean_nat_dec_eq(v_maxRecDepth_2169_, v___x_2172_);
if (v___x_2173_ == 0)
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_nat_dec_eq(v_currRecDepth_2164_, v_maxRecDepth_2169_);
if (v___x_2174_ == 0)
{
lean_inc(v_ref_2165_);
v___y_2153_ = v_ref_2165_;
v___y_2154_ = v_toCold_2163_;
v___y_2155_ = v_currRecDepth_2164_;
v___y_2156_ = v_isRecordingDeps_2168_;
v___y_2157_ = v_suppressElabErrors_2167_;
v___y_2158_ = v_optionFlags_2166_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2175_; 
lean_dec_ref(v_x_2137_);
lean_inc(v_ref_2165_);
v___x_2175_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2165_);
v___y_2143_ = v___x_2175_;
goto v___jp_2142_;
}
}
else
{
lean_inc(v_ref_2165_);
v___y_2153_ = v_ref_2165_;
v___y_2154_ = v_toCold_2163_;
v___y_2155_ = v_currRecDepth_2164_;
v___y_2156_ = v_isRecordingDeps_2168_;
v___y_2157_ = v_suppressElabErrors_2167_;
v___y_2158_ = v_optionFlags_2166_;
goto v___jp_2152_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2137_ = stack[0].m_obj;
lean_object* v___y_2138_ = stack[1].m_obj;
lean_object* v___y_2139_ = stack[2].m_obj;
lean_object* v___y_2140_ = stack[3].m_obj;
lean_object* v_res_2187_;
v_res_2187_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
stack->m_obj
 = v_res_2187_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
if (lean_obj_tag(v_x_2195_) == 0)
{
return v_x_2194_;
}
else
{
lean_object* v_key_2196_; lean_object* v_value_2197_; lean_object* v_tail_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2221_; 
v_key_2196_ = lean_ctor_get(v_x_2195_, 0);
v_value_2197_ = lean_ctor_get(v_x_2195_, 1);
v_tail_2198_ = lean_ctor_get(v_x_2195_, 2);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_x_2195_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2200_ = v_x_2195_;
v_isShared_2201_ = v_isSharedCheck_2221_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_tail_2198_);
lean_inc(v_value_2197_);
lean_inc(v_key_2196_);
lean_dec(v_x_2195_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2221_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; uint64_t v___x_2203_; uint64_t v___x_2204_; uint64_t v___x_2205_; uint64_t v_fold_2206_; uint64_t v___x_2207_; uint64_t v___x_2208_; uint64_t v___x_2209_; size_t v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2202_ = lean_array_get_size(v_x_2194_);
v___x_2203_ = l_Lean_ExprStructEq_hash(v_key_2196_);
v___x_2204_ = 32ULL;
v___x_2205_ = lean_uint64_shift_right(v___x_2203_, v___x_2204_);
v_fold_2206_ = lean_uint64_xor(v___x_2203_, v___x_2205_);
v___x_2207_ = 16ULL;
v___x_2208_ = lean_uint64_shift_right(v_fold_2206_, v___x_2207_);
v___x_2209_ = lean_uint64_xor(v_fold_2206_, v___x_2208_);
v___x_2210_ = lean_uint64_to_usize(v___x_2209_);
v___x_2211_ = lean_usize_of_nat(v___x_2202_);
v___x_2212_ = ((size_t)1ULL);
v___x_2213_ = lean_usize_sub(v___x_2211_, v___x_2212_);
v___x_2214_ = lean_usize_land(v___x_2210_, v___x_2213_);
v___x_2215_ = lean_array_uget_borrowed(v_x_2194_, v___x_2214_);
lean_inc(v___x_2215_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 2, v___x_2215_);
v___x_2217_ = v___x_2200_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_key_2196_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_value_2197_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_array_uset(v_x_2194_, v___x_2214_, v___x_2217_);
v_x_2194_ = v___x_2218_;
v_x_2195_ = v_tail_2198_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_2222_, lean_object* v_source_2223_, lean_object* v_target_2224_){
_start:
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = lean_array_get_size(v_source_2223_);
v___x_2226_ = lean_nat_dec_lt(v_i_2222_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_dec_ref(v_source_2223_);
lean_dec(v_i_2222_);
return v_target_2224_;
}
else
{
lean_object* v_es_2227_; lean_object* v___x_2228_; lean_object* v_source_2229_; lean_object* v_target_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_es_2227_ = lean_array_fget(v_source_2223_, v_i_2222_);
v___x_2228_ = lean_box(0);
v_source_2229_ = lean_array_fset(v_source_2223_, v_i_2222_, v___x_2228_);
v_target_2230_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_2224_, v_es_2227_);
v___x_2231_ = lean_unsigned_to_nat(1u);
v___x_2232_ = lean_nat_add(v_i_2222_, v___x_2231_);
lean_dec(v_i_2222_);
v_i_2222_ = v___x_2232_;
v_source_2223_ = v_source_2229_;
v_target_2224_ = v_target_2230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v_nbuckets_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2235_ = lean_array_get_size(v_data_2234_);
v___x_2236_ = lean_unsigned_to_nat(2u);
v_nbuckets_2237_ = lean_nat_mul(v___x_2235_, v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_mk_array(v_nbuckets_2237_, v___x_2239_);
v___x_2241_ = lean_array_propagate_mark(v_data_2234_, v___x_2240_);
v___x_2242_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_2238_, v_data_2234_, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_2243_, lean_object* v_b_2244_, lean_object* v_x_2245_){
_start:
{
if (lean_obj_tag(v_x_2245_) == 0)
{
lean_dec(v_b_2244_);
lean_dec_ref(v_a_2243_);
return v_x_2245_;
}
else
{
lean_object* v_key_2246_; lean_object* v_value_2247_; lean_object* v_tail_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2260_; 
v_key_2246_ = lean_ctor_get(v_x_2245_, 0);
v_value_2247_ = lean_ctor_get(v_x_2245_, 1);
v_tail_2248_ = lean_ctor_get(v_x_2245_, 2);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_x_2245_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2250_ = v_x_2245_;
v_isShared_2251_ = v_isSharedCheck_2260_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_tail_2248_);
lean_inc(v_value_2247_);
lean_inc(v_key_2246_);
lean_dec(v_x_2245_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2260_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
uint8_t v___x_2252_; 
v___x_2252_ = l_Lean_ExprStructEq_beq(v_key_2246_, v_a_2243_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2243_, v_b_2244_, v_tail_2248_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 2, v___x_2253_);
v___x_2255_ = v___x_2250_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_key_2246_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_value_2247_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
else
{
lean_object* v___x_2258_; 
lean_dec(v_value_2247_);
lean_dec(v_key_2246_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_b_2244_);
lean_ctor_set(v___x_2250_, 0, v_a_2243_);
v___x_2258_ = v___x_2250_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2243_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_b_2244_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_tail_2248_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_2261_, lean_object* v_x_2262_){
_start:
{
if (lean_obj_tag(v_x_2262_) == 0)
{
uint8_t v___x_2263_; 
v___x_2263_ = 0;
return v___x_2263_;
}
else
{
lean_object* v_key_2264_; lean_object* v_tail_2265_; uint8_t v___x_2266_; 
v_key_2264_ = lean_ctor_get(v_x_2262_, 0);
v_tail_2265_ = lean_ctor_get(v_x_2262_, 2);
v___x_2266_ = l_Lean_ExprStructEq_beq(v_key_2264_, v_a_2261_);
if (v___x_2266_ == 0)
{
v_x_2262_ = v_tail_2265_;
goto _start;
}
else
{
return v___x_2266_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2261_ = stack[0].m_obj;
lean_object* v_x_2262_ = stack[1].m_obj;
uint8_t v_res_2268_;
v_res_2268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2261_, v_x_2262_);
stack->m_num = v_res_2268_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_2269_, lean_object* v_x_2270_){
_start:
{
uint8_t v_res_2271_; lean_object* v_r_2272_; 
v_res_2271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2269_, v_x_2270_);
lean_dec(v_x_2270_);
lean_dec_ref(v_a_2269_);
v_r_2272_ = lean_box(v_res_2271_);
return v_r_2272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object* v_m_2273_, lean_object* v_a_2274_, lean_object* v_b_2275_){
_start:
{
lean_object* v_size_2276_; lean_object* v_buckets_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2320_; 
v_size_2276_ = lean_ctor_get(v_m_2273_, 0);
v_buckets_2277_ = lean_ctor_get(v_m_2273_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_m_2273_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2279_ = v_m_2273_;
v_isShared_2280_ = v_isSharedCheck_2320_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_buckets_2277_);
lean_inc(v_size_2276_);
lean_dec(v_m_2273_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2320_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; uint64_t v___x_2282_; uint64_t v___x_2283_; uint64_t v___x_2284_; uint64_t v_fold_2285_; uint64_t v___x_2286_; uint64_t v___x_2287_; uint64_t v___x_2288_; size_t v___x_2289_; size_t v___x_2290_; size_t v___x_2291_; size_t v___x_2292_; size_t v___x_2293_; lean_object* v_bkt_2294_; uint8_t v___x_2295_; 
v___x_2281_ = lean_array_get_size(v_buckets_2277_);
v___x_2282_ = l_Lean_ExprStructEq_hash(v_a_2274_);
v___x_2283_ = 32ULL;
v___x_2284_ = lean_uint64_shift_right(v___x_2282_, v___x_2283_);
v_fold_2285_ = lean_uint64_xor(v___x_2282_, v___x_2284_);
v___x_2286_ = 16ULL;
v___x_2287_ = lean_uint64_shift_right(v_fold_2285_, v___x_2286_);
v___x_2288_ = lean_uint64_xor(v_fold_2285_, v___x_2287_);
v___x_2289_ = lean_uint64_to_usize(v___x_2288_);
v___x_2290_ = lean_usize_of_nat(v___x_2281_);
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_sub(v___x_2290_, v___x_2291_);
v___x_2293_ = lean_usize_land(v___x_2289_, v___x_2292_);
v_bkt_2294_ = lean_array_uget_borrowed(v_buckets_2277_, v___x_2293_);
v___x_2295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2274_, v_bkt_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v_size_x27_2297_; lean_object* v___x_2298_; lean_object* v_buckets_x27_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2296_ = lean_unsigned_to_nat(1u);
v_size_x27_2297_ = lean_nat_add(v_size_2276_, v___x_2296_);
lean_dec(v_size_2276_);
lean_inc(v_bkt_2294_);
v___x_2298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2298_, 0, v_a_2274_);
lean_ctor_set(v___x_2298_, 1, v_b_2275_);
lean_ctor_set(v___x_2298_, 2, v_bkt_2294_);
v_buckets_x27_2299_ = lean_array_uset(v_buckets_2277_, v___x_2293_, v___x_2298_);
v___x_2300_ = lean_unsigned_to_nat(4u);
v___x_2301_ = lean_nat_mul(v_size_x27_2297_, v___x_2300_);
v___x_2302_ = lean_unsigned_to_nat(3u);
v___x_2303_ = lean_nat_div(v___x_2301_, v___x_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_array_get_size(v_buckets_x27_2299_);
v___x_2305_ = lean_nat_dec_le(v___x_2303_, v___x_2304_);
lean_dec(v___x_2303_);
if (v___x_2305_ == 0)
{
lean_object* v_val_2306_; lean_object* v___x_2308_; 
v_val_2306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_2299_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v_val_2306_);
lean_ctor_set(v___x_2279_, 0, v_size_x27_2297_);
v___x_2308_ = v___x_2279_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_size_x27_2297_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_val_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v___x_2311_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v_buckets_x27_2299_);
lean_ctor_set(v___x_2279_, 0, v_size_x27_2297_);
v___x_2311_ = v___x_2279_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_size_x27_2297_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_buckets_x27_2299_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
else
{
lean_object* v___x_2313_; lean_object* v_buckets_x27_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_inc(v_bkt_2294_);
v___x_2313_ = lean_box(0);
v_buckets_x27_2314_ = lean_array_uset(v_buckets_2277_, v___x_2293_, v___x_2313_);
v___x_2315_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2274_, v_b_2275_, v_bkt_2294_);
v___x_2316_ = lean_array_uset(v_buckets_x27_2314_, v___x_2293_, v___x_2315_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v___x_2316_);
v___x_2318_ = v___x_2279_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_size_2276_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object* v_a_2321_, lean_object* v_e_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2325_ = lean_st_ref_take(v_a_2321_);
v___x_2326_ = lean_box(0);
v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2325_, v_e_2322_, v_a_2323_);
v___x_2328_ = lean_st_ref_put(v_a_2321_, v___x_2327_);
return v___x_2326_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2321_ = stack[0].m_obj;
lean_object* v_e_2322_ = stack[1].m_obj;
lean_object* v_a_2323_ = stack[2].m_obj;
lean_object* v_res_2329_;
v_res_2329_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2321_, v_e_2322_, v_a_2323_);
stack->m_obj
 = v_res_2329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2330_, lean_object* v_e_2331_, lean_object* v_a_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2330_, v_e_2331_, v_a_2332_);
lean_dec(v_a_2330_);
return v_res_2334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2336_; lean_object* v_dummy_2337_; 
v___x_2336_ = lean_box(0);
v_dummy_2337_ = l_Lean_Expr_sort___override(v___x_2336_);
return v_dummy_2337_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object* v_pre_2338_, lean_object* v_post_2339_, size_t v_sz_2340_, size_t v_i_2341_, lean_object* v_bs_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_usize_dec_lt(v_i_2341_, v_sz_2340_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec_ref(v_post_2339_);
lean_dec_ref(v_pre_2338_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_bs_2342_);
return v___x_2348_;
}
else
{
lean_object* v_v_2349_; lean_object* v___x_2350_; lean_object* v_bs_x27_2351_; lean_object* v___x_2352_; 
v_v_2349_ = lean_array_uget(v_bs_2342_, v_i_2341_);
v___x_2350_ = lean_unsigned_to_nat(0u);
v_bs_x27_2351_ = lean_array_uset(v_bs_2342_, v_i_2341_, v___x_2350_);
lean_inc_ref(v_post_2339_);
lean_inc_ref(v_pre_2338_);
v___x_2352_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2338_, v_post_2339_, v_v_2349_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = ((size_t)1ULL);
v___x_2355_ = lean_usize_add(v_i_2341_, v___x_2354_);
v___x_2356_ = lean_array_uset(v_bs_x27_2351_, v_i_2341_, v_a_2353_);
v_i_2341_ = v___x_2355_;
v_bs_2342_ = v___x_2356_;
goto _start;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v_bs_x27_2351_);
lean_dec_ref(v_post_2339_);
lean_dec_ref(v_pre_2338_);
v_a_2358_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2352_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2352_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2338_ = stack[0].m_obj;
lean_object* v_post_2339_ = stack[1].m_obj;
size_t v_sz_2340_ = stack[2].m_num;
size_t v_i_2341_ = stack[3].m_num;
lean_object* v_bs_2342_ = stack[4].m_obj;
lean_object* v___y_2343_ = stack[5].m_obj;
lean_object* v___y_2344_ = stack[6].m_obj;
lean_object* v___y_2345_ = stack[7].m_obj;
lean_object* v_res_2366_;
v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2338_, v_post_2339_, v_sz_2340_, v_i_2341_, v_bs_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
stack->m_obj
 = v_res_2366_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object* v_pre_2367_, lean_object* v_post_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
if (lean_obj_tag(v_x_2369_) == 5)
{
lean_object* v_fn_2376_; lean_object* v_arg_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_fn_2376_ = lean_ctor_get(v_x_2369_, 0);
lean_inc_ref(v_fn_2376_);
v_arg_2377_ = lean_ctor_get(v_x_2369_, 1);
lean_inc_ref(v_arg_2377_);
lean_dec_ref_known(v_x_2369_, 2);
v___x_2378_ = lean_array_set(v_x_2370_, v_x_2371_, v_arg_2377_);
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_nat_sub(v_x_2371_, v___x_2379_);
lean_dec(v_x_2371_);
v_x_2369_ = v_fn_2376_;
v_x_2370_ = v___x_2378_;
v_x_2371_ = v___x_2380_;
goto _start;
}
else
{
lean_object* v___x_2382_; 
lean_dec(v_x_2371_);
lean_inc_ref(v_post_2368_);
lean_inc_ref(v_pre_2367_);
v___x_2382_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2367_, v_post_2368_, v_x_2369_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; size_t v_sz_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v_sz_2384_ = lean_array_size(v_x_2370_);
v___x_2385_ = ((size_t)0ULL);
lean_inc_ref(v_post_2368_);
lean_inc_ref(v_pre_2367_);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2367_, v_post_2368_, v_sz_2384_, v___x_2385_, v_x_2370_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = l_Lean_mkAppN(v_a_2383_, v_a_2387_);
lean_dec(v_a_2387_);
v___x_2389_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2367_, v_post_2368_, v___x_2388_, v___y_2372_, v___y_2373_, v___y_2374_);
return v___x_2389_;
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_a_2383_);
lean_dec_ref(v_post_2368_);
lean_dec_ref(v_pre_2367_);
v_a_2390_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2386_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2386_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_dec_ref(v_x_2370_);
lean_dec_ref(v_post_2368_);
lean_dec_ref(v_pre_2367_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2367_ = stack[0].m_obj;
lean_object* v_post_2368_ = stack[1].m_obj;
lean_object* v_x_2369_ = stack[2].m_obj;
lean_object* v_x_2370_ = stack[3].m_obj;
lean_object* v_x_2371_ = stack[4].m_obj;
lean_object* v___y_2372_ = stack[5].m_obj;
lean_object* v___y_2373_ = stack[6].m_obj;
lean_object* v___y_2374_ = stack[7].m_obj;
lean_object* v_res_2398_;
v_res_2398_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2367_, v_post_2368_, v_x_2369_, v_x_2370_, v_x_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
stack->m_obj
 = v_res_2398_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object* v___x_2399_, lean_object* v_pre_2400_, lean_object* v_e_2401_, lean_object* v_post_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Core_checkSystem(v___x_2399_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
lean_dec_ref_known(v___x_2407_, 1);
lean_inc_ref(v_pre_2400_);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
lean_inc_ref(v_e_2401_);
v___x_2408_ = lean_apply_4(v_pre_2400_, v_e_2401_, v___y_2404_, v___y_2405_, lean_box(0));
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2524_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2524_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2524_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___y_2414_; 
switch(lean_obj_tag(v_a_2409_))
{
case 0:
{
lean_object* v_e_2514_; lean_object* v___x_2516_; 
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_e_2401_);
lean_dec_ref(v_pre_2400_);
v_e_2514_ = lean_ctor_get(v_a_2409_, 0);
lean_inc_ref(v_e_2514_);
lean_dec_ref_known(v_a_2409_, 1);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v_e_2514_);
v___x_2516_ = v___x_2411_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_e_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
case 1:
{
lean_object* v_e_2518_; lean_object* v___x_2519_; 
lean_del_object(v___x_2411_);
lean_dec_ref(v_e_2401_);
v_e_2518_ = lean_ctor_get(v_a_2409_, 0);
lean_inc_ref(v_e_2518_);
lean_dec_ref_known(v_a_2409_, 1);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_e_2518_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2521_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v_a_2520_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2521_;
}
else
{
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2519_;
}
}
default: 
{
lean_object* v_e_x3f_2522_; 
lean_del_object(v___x_2411_);
v_e_x3f_2522_ = lean_ctor_get(v_a_2409_, 0);
lean_inc(v_e_x3f_2522_);
lean_dec_ref_known(v_a_2409_, 1);
if (lean_obj_tag(v_e_x3f_2522_) == 0)
{
v___y_2414_ = v_e_2401_;
goto v___jp_2413_;
}
else
{
lean_object* v_val_2523_; 
lean_dec_ref(v_e_2401_);
v_val_2523_ = lean_ctor_get(v_e_x3f_2522_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v_e_x3f_2522_, 1);
v___y_2414_ = v_val_2523_;
goto v___jp_2413_;
}
}
}
v___jp_2413_:
{
switch(lean_obj_tag(v___y_2414_))
{
case 7:
{
lean_object* v_binderName_2415_; lean_object* v_binderType_2416_; lean_object* v_body_2417_; uint8_t v_binderInfo_2418_; lean_object* v___x_2419_; 
v_binderName_2415_ = lean_ctor_get(v___y_2414_, 0);
v_binderType_2416_ = lean_ctor_get(v___y_2414_, 1);
v_body_2417_ = lean_ctor_get(v___y_2414_, 2);
v_binderInfo_2418_ = lean_ctor_get_uint8(v___y_2414_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2416_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2419_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_binderType_2416_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
lean_inc_ref(v_body_2417_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_body_2417_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; size_t v___x_2423_; size_t v___x_2424_; uint8_t v___x_2425_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = lean_ptr_addr(v_binderType_2416_);
v___x_2424_ = lean_ptr_addr(v_a_2420_);
v___x_2425_ = lean_usize_dec_eq(v___x_2423_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
lean_inc(v_binderName_2415_);
lean_dec_ref_known(v___y_2414_, 3);
v___x_2426_ = l_Lean_Expr_forallE___override(v_binderName_2415_, v_a_2420_, v_a_2422_, v_binderInfo_2418_);
v___x_2427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2426_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2427_;
}
else
{
size_t v___x_2428_; size_t v___x_2429_; uint8_t v___x_2430_; 
v___x_2428_ = lean_ptr_addr(v_body_2417_);
v___x_2429_ = lean_ptr_addr(v_a_2422_);
v___x_2430_ = lean_usize_dec_eq(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_inc(v_binderName_2415_);
lean_dec_ref_known(v___y_2414_, 3);
v___x_2431_ = l_Lean_Expr_forallE___override(v_binderName_2415_, v_a_2420_, v_a_2422_, v_binderInfo_2418_);
v___x_2432_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2431_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2432_;
}
else
{
uint8_t v___x_2433_; 
v___x_2433_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2418_, v_binderInfo_2418_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_inc(v_binderName_2415_);
lean_dec_ref_known(v___y_2414_, 3);
v___x_2434_ = l_Lean_Expr_forallE___override(v_binderName_2415_, v_a_2420_, v_a_2422_, v_binderInfo_2418_);
v___x_2435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2434_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2435_;
}
else
{
lean_object* v___x_2436_; 
lean_dec(v_a_2422_);
lean_dec(v_a_2420_);
v___x_2436_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___y_2414_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2436_;
}
}
}
}
else
{
lean_dec(v_a_2420_);
lean_dec_ref_known(v___y_2414_, 3);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2421_;
}
}
else
{
lean_dec_ref_known(v___y_2414_, 3);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2419_;
}
}
case 6:
{
lean_object* v_binderName_2437_; lean_object* v_binderType_2438_; lean_object* v_body_2439_; uint8_t v_binderInfo_2440_; lean_object* v___x_2441_; 
v_binderName_2437_ = lean_ctor_get(v___y_2414_, 0);
v_binderType_2438_ = lean_ctor_get(v___y_2414_, 1);
v_body_2439_ = lean_ctor_get(v___y_2414_, 2);
v_binderInfo_2440_ = lean_ctor_get_uint8(v___y_2414_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2438_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_binderType_2438_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
lean_inc_ref(v_body_2439_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_body_2439_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; size_t v___x_2445_; size_t v___x_2446_; uint8_t v___x_2447_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = lean_ptr_addr(v_binderType_2438_);
v___x_2446_ = lean_ptr_addr(v_a_2442_);
v___x_2447_ = lean_usize_dec_eq(v___x_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_inc(v_binderName_2437_);
lean_dec_ref_known(v___y_2414_, 3);
v___x_2448_ = l_Lean_Expr_lam___override(v_binderName_2437_, v_a_2442_, v_a_2444_, v_binderInfo_2440_);
v___x_2449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2448_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2449_;
}
else
{
size_t v___x_2450_; size_t v___x_2451_; uint8_t v___x_2452_; 
v___x_2450_ = lean_ptr_addr(v_body_2439_);
v___x_2451_ = lean_ptr_addr(v_a_2444_);
v___x_2452_ = lean_usize_dec_eq(v___x_2450_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_inc(v_binderName_2437_);
lean_dec_ref_known(v___y_2414_, 3);
v___x_2453_ = l_Lean_Expr_lam___override(v_binderName_2437_, v_a_2442_, v_a_2444_, v_binderInfo_2440_);
v___x_2454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2453_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2454_;
}
else
{
uint8_t v___x_2455_; 
v___x_2455_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2440_, v_binderInfo_2440_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_inc(v_binderName_2437_);
lean_dec_ref_known(v___y_2414_, 3);
v___x_2456_ = l_Lean_Expr_lam___override(v_binderName_2437_, v_a_2442_, v_a_2444_, v_binderInfo_2440_);
v___x_2457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2456_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; 
lean_dec(v_a_2444_);
lean_dec(v_a_2442_);
v___x_2458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___y_2414_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2458_;
}
}
}
}
else
{
lean_dec(v_a_2442_);
lean_dec_ref_known(v___y_2414_, 3);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2443_;
}
}
else
{
lean_dec_ref_known(v___y_2414_, 3);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2441_;
}
}
case 8:
{
lean_object* v_declName_2459_; lean_object* v_type_2460_; lean_object* v_value_2461_; lean_object* v_body_2462_; uint8_t v_nondep_2463_; lean_object* v___x_2464_; 
v_declName_2459_ = lean_ctor_get(v___y_2414_, 0);
v_type_2460_ = lean_ctor_get(v___y_2414_, 1);
v_value_2461_ = lean_ctor_get(v___y_2414_, 2);
v_body_2462_ = lean_ctor_get(v___y_2414_, 3);
v_nondep_2463_ = lean_ctor_get_uint8(v___y_2414_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2460_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_type_2460_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
lean_inc_ref(v_value_2461_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_value_2461_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
lean_inc_ref(v_body_2462_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_body_2462_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; size_t v___x_2470_; size_t v___x_2471_; uint8_t v___x_2472_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = lean_ptr_addr(v_type_2460_);
v___x_2471_ = lean_ptr_addr(v_a_2465_);
v___x_2472_ = lean_usize_dec_eq(v___x_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_inc(v_declName_2459_);
lean_dec_ref_known(v___y_2414_, 4);
v___x_2473_ = l_Lean_Expr_letE___override(v_declName_2459_, v_a_2465_, v_a_2467_, v_a_2469_, v_nondep_2463_);
v___x_2474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2473_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2474_;
}
else
{
size_t v___x_2475_; size_t v___x_2476_; uint8_t v___x_2477_; 
v___x_2475_ = lean_ptr_addr(v_value_2461_);
v___x_2476_ = lean_ptr_addr(v_a_2467_);
v___x_2477_ = lean_usize_dec_eq(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_inc(v_declName_2459_);
lean_dec_ref_known(v___y_2414_, 4);
v___x_2478_ = l_Lean_Expr_letE___override(v_declName_2459_, v_a_2465_, v_a_2467_, v_a_2469_, v_nondep_2463_);
v___x_2479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2478_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2479_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; uint8_t v___x_2482_; 
v___x_2480_ = lean_ptr_addr(v_body_2462_);
v___x_2481_ = lean_ptr_addr(v_a_2469_);
v___x_2482_ = lean_usize_dec_eq(v___x_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_inc(v_declName_2459_);
lean_dec_ref_known(v___y_2414_, 4);
v___x_2483_ = l_Lean_Expr_letE___override(v_declName_2459_, v_a_2465_, v_a_2467_, v_a_2469_, v_nondep_2463_);
v___x_2484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2483_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; 
lean_dec(v_a_2469_);
lean_dec(v_a_2467_);
lean_dec(v_a_2465_);
v___x_2485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___y_2414_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2485_;
}
}
}
}
else
{
lean_dec(v_a_2467_);
lean_dec(v_a_2465_);
lean_dec_ref_known(v___y_2414_, 4);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2468_;
}
}
else
{
lean_dec(v_a_2465_);
lean_dec_ref_known(v___y_2414_, 4);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2466_;
}
}
else
{
lean_dec_ref_known(v___y_2414_, 4);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2464_;
}
}
case 5:
{
lean_object* v_dummy_2486_; lean_object* v_nargs_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_dummy_2486_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_2487_ = l_Lean_Expr_getAppNumArgs(v___y_2414_);
lean_inc(v_nargs_2487_);
v___x_2488_ = lean_mk_array(v_nargs_2487_, v_dummy_2486_);
v___x_2489_ = lean_unsigned_to_nat(1u);
v___x_2490_ = lean_nat_sub(v_nargs_2487_, v___x_2489_);
lean_dec(v_nargs_2487_);
v___x_2491_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2400_, v_post_2402_, v___y_2414_, v___x_2488_, v___x_2490_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2491_;
}
case 10:
{
lean_object* v_data_2492_; lean_object* v_expr_2493_; lean_object* v___x_2494_; 
v_data_2492_ = lean_ctor_get(v___y_2414_, 0);
v_expr_2493_ = lean_ctor_get(v___y_2414_, 1);
lean_inc_ref(v_expr_2493_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2494_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_expr_2493_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; size_t v___x_2496_; size_t v___x_2497_; uint8_t v___x_2498_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = lean_ptr_addr(v_expr_2493_);
v___x_2497_ = lean_ptr_addr(v_a_2495_);
v___x_2498_ = lean_usize_dec_eq(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_inc(v_data_2492_);
lean_dec_ref_known(v___y_2414_, 2);
v___x_2499_ = l_Lean_Expr_mdata___override(v_data_2492_, v_a_2495_);
v___x_2500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2499_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2500_;
}
else
{
lean_object* v___x_2501_; 
lean_dec(v_a_2495_);
v___x_2501_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___y_2414_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2501_;
}
}
else
{
lean_dec_ref_known(v___y_2414_, 2);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2494_;
}
}
case 11:
{
lean_object* v_typeName_2502_; lean_object* v_idx_2503_; lean_object* v_struct_2504_; lean_object* v___x_2505_; 
v_typeName_2502_ = lean_ctor_get(v___y_2414_, 0);
v_idx_2503_ = lean_ctor_get(v___y_2414_, 1);
v_struct_2504_ = lean_ctor_get(v___y_2414_, 2);
lean_inc_ref(v_struct_2504_);
lean_inc_ref(v_post_2402_);
lean_inc_ref(v_pre_2400_);
v___x_2505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2400_, v_post_2402_, v_struct_2504_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; size_t v___x_2507_; size_t v___x_2508_; uint8_t v___x_2509_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_ptr_addr(v_struct_2504_);
v___x_2508_ = lean_ptr_addr(v_a_2506_);
v___x_2509_ = lean_usize_dec_eq(v___x_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_inc(v_idx_2503_);
lean_inc(v_typeName_2502_);
lean_dec_ref_known(v___y_2414_, 3);
v___x_2510_ = l_Lean_Expr_proj___override(v_typeName_2502_, v_idx_2503_, v_a_2506_);
v___x_2511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___x_2510_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2511_;
}
else
{
lean_object* v___x_2512_; 
lean_dec(v_a_2506_);
v___x_2512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___y_2414_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2512_;
}
}
else
{
lean_dec_ref_known(v___y_2414_, 3);
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_pre_2400_);
return v___x_2505_;
}
}
default: 
{
lean_object* v___x_2513_; 
v___x_2513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2400_, v_post_2402_, v___y_2414_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2513_;
}
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_e_2401_);
lean_dec_ref(v_pre_2400_);
v_a_2525_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2408_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2408_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v_post_2402_);
lean_dec_ref(v_e_2401_);
lean_dec_ref(v_pre_2400_);
v_a_2533_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2407_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2407_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2399_ = stack[0].m_obj;
lean_object* v_pre_2400_ = stack[1].m_obj;
lean_object* v_e_2401_ = stack[2].m_obj;
lean_object* v_post_2402_ = stack[3].m_obj;
lean_object* v___y_2403_ = stack[4].m_obj;
lean_object* v___y_2404_ = stack[5].m_obj;
lean_object* v___y_2405_ = stack[6].m_obj;
lean_object* v_res_2541_;
v_res_2541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_2399_, v_pre_2400_, v_e_2401_, v_post_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2542_, lean_object* v_pre_2543_, lean_object* v_e_2544_, lean_object* v_post_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_2542_, v_pre_2543_, v_e_2544_, v_post_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
return v_res_2550_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object* v_pre_2551_, lean_object* v_post_2552_, lean_object* v_e_2553_, lean_object* v_a_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_inc(v_a_2554_);
v___x_2558_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2558_, 0, lean_box(0));
lean_closure_set(v___x_2558_, 1, lean_box(0));
lean_closure_set(v___x_2558_, 2, v_a_2554_);
v___x_2559_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___x_2558_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2591_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2591_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2591_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_2560_, v_e_2553_);
lean_dec(v_a_2560_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; 
lean_del_object(v___x_2562_);
v___x_2565_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_2553_);
v___f_2566_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2566_, 0, v___x_2565_);
lean_closure_set(v___f_2566_, 1, v_pre_2551_);
lean_closure_set(v___f_2566_, 2, v_e_2553_);
lean_closure_set(v___f_2566_, 3, v_post_2552_);
v___x_2567_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2566_, v_a_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_n(v_a_2568_, 2);
lean_dec_ref_known(v___x_2567_, 1);
lean_inc(v_a_2554_);
v___f_2569_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2569_, 0, v_a_2554_);
lean_closure_set(v___f_2569_, 1, v_e_2553_);
lean_closure_set(v___f_2569_, 2, v_a_2568_);
v___x_2570_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___f_2569_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2570_, 0);
lean_dec(v_unused_2578_);
v___x_2572_ = v___x_2570_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_dec(v___x_2570_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v_a_2568_);
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2568_);
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
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_a_2568_);
v_a_2579_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2570_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2570_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_dec_ref(v_e_2553_);
return v___x_2567_;
}
}
else
{
lean_object* v_val_2587_; lean_object* v___x_2589_; 
lean_dec_ref(v_e_2553_);
lean_dec_ref(v_post_2552_);
lean_dec_ref(v_pre_2551_);
v_val_2587_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v___x_2564_, 1);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_val_2587_);
v___x_2589_ = v___x_2562_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_val_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_e_2553_);
lean_dec_ref(v_post_2552_);
lean_dec_ref(v_pre_2551_);
v_a_2592_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2559_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2559_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2551_ = stack[0].m_obj;
lean_object* v_post_2552_ = stack[1].m_obj;
lean_object* v_e_2553_ = stack[2].m_obj;
lean_object* v_a_2554_ = stack[3].m_obj;
lean_object* v___y_2555_ = stack[4].m_obj;
lean_object* v___y_2556_ = stack[5].m_obj;
lean_object* v_res_2600_;
v_res_2600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2551_, v_post_2552_, v_e_2553_, v_a_2554_, v___y_2555_, v___y_2556_);
stack->m_obj
 = v_res_2600_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object* v_pre_2601_, lean_object* v_post_2602_, lean_object* v_e_2603_, lean_object* v_a_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
lean_inc_ref(v_post_2602_);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc_ref(v_e_2603_);
v___x_2608_ = lean_apply_4(v_post_2602_, v_e_2603_, v___y_2605_, v___y_2606_, lean_box(0));
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2627_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2627_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2627_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
switch(lean_obj_tag(v_a_2609_))
{
case 0:
{
lean_object* v_e_2613_; lean_object* v___x_2615_; 
lean_dec_ref(v_e_2603_);
lean_dec_ref(v_post_2602_);
lean_dec_ref(v_pre_2601_);
v_e_2613_ = lean_ctor_get(v_a_2609_, 0);
lean_inc_ref(v_e_2613_);
lean_dec_ref_known(v_a_2609_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_e_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_e_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
case 1:
{
lean_object* v_e_2617_; lean_object* v___x_2618_; 
lean_del_object(v___x_2611_);
lean_dec_ref(v_e_2603_);
v_e_2617_ = lean_ctor_get(v_a_2609_, 0);
lean_inc_ref(v_e_2617_);
lean_dec_ref_known(v_a_2609_, 1);
v___x_2618_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2601_, v_post_2602_, v_e_2617_, v_a_2604_, v___y_2605_, v___y_2606_);
return v___x_2618_;
}
default: 
{
lean_object* v_e_x3f_2619_; 
lean_dec_ref(v_post_2602_);
lean_dec_ref(v_pre_2601_);
v_e_x3f_2619_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_e_x3f_2619_);
lean_dec_ref_known(v_a_2609_, 1);
if (lean_obj_tag(v_e_x3f_2619_) == 0)
{
lean_object* v___x_2621_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_e_2603_);
v___x_2621_ = v___x_2611_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_e_2603_);
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
lean_object* v_val_2623_; lean_object* v___x_2625_; 
lean_dec_ref(v_e_2603_);
v_val_2623_ = lean_ctor_get(v_e_x3f_2619_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v_e_x3f_2619_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_val_2623_);
v___x_2625_ = v___x_2611_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_val_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v_e_2603_);
lean_dec_ref(v_post_2602_);
lean_dec_ref(v_pre_2601_);
v_a_2628_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2608_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2608_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2601_ = stack[0].m_obj;
lean_object* v_post_2602_ = stack[1].m_obj;
lean_object* v_e_2603_ = stack[2].m_obj;
lean_object* v_a_2604_ = stack[3].m_obj;
lean_object* v___y_2605_ = stack[4].m_obj;
lean_object* v___y_2606_ = stack[5].m_obj;
lean_object* v_res_2636_;
v_res_2636_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2601_, v_post_2602_, v_e_2603_, v_a_2604_, v___y_2605_, v___y_2606_);
stack->m_obj
 = v_res_2636_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2637_, lean_object* v_post_2638_, lean_object* v_e_2639_, lean_object* v_a_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2637_, v_post_2638_, v_e_2639_, v_a_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v_a_2640_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2645_, lean_object* v_post_2646_, lean_object* v_sz_2647_, lean_object* v_i_2648_, lean_object* v_bs_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2647_);
lean_dec(v_sz_2647_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2645_, v_post_2646_, v_sz_boxed_2654_, v_i_boxed_2655_, v_bs_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_2657_, lean_object* v_post_2658_, lean_object* v_x_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2657_, v_post_2658_, v_x_2659_, v_x_2660_, v_x_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(lean_object* v_pre_2667_, lean_object* v_post_2668_, lean_object* v_e_2669_, lean_object* v_a_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2667_, v_post_2668_, v_e_2669_, v_a_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v_a_2670_);
return v_res_2674_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_unsigned_to_nat(16u);
v___x_2677_ = lean_mk_array(v___x_2676_, v___x_2675_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
v___x_2679_ = lean_unsigned_to_nat(0u);
v___x_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
lean_ctor_set(v___x_2680_, 1, v___x_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
v___x_2682_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2682_, 0, lean_box(0));
lean_closure_set(v___x_2682_, 1, lean_box(0));
lean_closure_set(v___x_2682_, 2, v___x_2681_);
return v___x_2682_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object* v_input_2683_, lean_object* v_pre_2684_, lean_object* v_post_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v_a_2691_; lean_object* v___x_2692_; 
v___x_2689_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_2690_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2689_, v___y_2686_, v___y_2687_);
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
v___x_2692_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2684_, v_post_2685_, v_input_2683_, v_a_2691_, v___y_2686_, v___y_2687_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2694_, 0, lean_box(0));
lean_closure_set(v___x_2694_, 1, lean_box(0));
lean_closure_set(v___x_2694_, 2, v_a_2691_);
v___x_2695_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2694_, v___y_2686_, v___y_2687_);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2695_, 0);
lean_dec(v_unused_2703_);
v___x_2697_ = v___x_2695_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_dec(v___x_2695_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v_a_2693_);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2693_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
lean_dec(v_a_2691_);
return v___x_2692_;
}
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_2683_ = stack[0].m_obj;
lean_object* v_pre_2684_ = stack[1].m_obj;
lean_object* v_post_2685_ = stack[2].m_obj;
lean_object* v___y_2686_ = stack[3].m_obj;
lean_object* v___y_2687_ = stack[4].m_obj;
lean_object* v_res_2704_;
v_res_2704_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2683_, v_pre_2684_, v_post_2685_, v___y_2686_, v___y_2687_);
stack->m_obj
 = v_res_2704_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object* v_input_2705_, lean_object* v_pre_2706_, lean_object* v_post_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2705_, v_pre_2706_, v_post_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2711_;
}
}
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* v_e_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___f_2719_; lean_object* v___x_2720_; 
v___f_2719_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0));
v___x_2720_ = lean_find_expr(v___f_2719_, v_e_2715_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_e_2715_);
return v___x_2721_;
}
else
{
lean_object* v_pre_2722_; lean_object* v___f_2723_; lean_object* v___x_2724_; 
lean_dec_ref_known(v___x_2720_, 1);
v_pre_2722_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1));
v___f_2723_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2));
v___x_2724_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_e_2715_, v_pre_2722_, v___f_2723_, v_a_2716_, v_a_2717_);
return v___x_2724_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_eraseIrrelevantMData_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2715_ = stack[0].m_obj;
lean_object* v_a_2716_ = stack[1].m_obj;
lean_object* v_a_2717_ = stack[2].m_obj;
lean_object* v_res_2725_;
v_res_2725_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2715_, v_a_2716_, v_a_2717_);
stack->m_obj
 = v_res_2725_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object* v_e_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2731_, lean_object* v_m_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2732_, v_a_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2735_, lean_object* v_m_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_2735_, v_m_2736_, v_a_2737_);
lean_dec_ref(v_a_2737_);
lean_dec_ref(v_m_2736_);
return v_res_2738_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_2739_, lean_object* v_ref_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2740_);
return v___x_2744_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2740_ = stack[1].m_obj;
lean_object* v___y_2741_ = stack[2].m_obj;
lean_object* v___y_2742_ = stack[3].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_box(0), v_ref_2740_, v___y_2741_, v___y_2742_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2746_, lean_object* v_ref_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2746_, v_ref_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2751_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_2756_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2753_ = stack[1].m_obj;
lean_object* v___y_2754_ = stack[2].m_obj;
lean_object* v_res_2757_;
v_res_2757_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(lean_box(0), v___y_2753_, v___y_2754_);
stack->m_obj
 = v_res_2757_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2762_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_2763_, lean_object* v_x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2764_ = stack[1].m_obj;
lean_object* v___y_2765_ = stack[2].m_obj;
lean_object* v___y_2766_ = stack[3].m_obj;
lean_object* v___y_2767_ = stack[4].m_obj;
lean_object* v_res_2770_;
v_res_2770_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_box(0), v_x_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
stack->m_obj
 = v_res_2770_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2771_, lean_object* v_x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_2771_, v_x_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2778_, lean_object* v_m_2779_, lean_object* v_a_2780_, lean_object* v_b_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2779_, v_a_2780_, v_b_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_2783_, lean_object* v_a_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2787_, lean_object* v_a_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2787_, v_a_2788_, v_x_2789_);
lean_dec(v_x_2789_);
lean_dec_ref(v_a_2788_);
return v_res_2790_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_2791_, lean_object* v_a_2792_, lean_object* v_x_2793_){
_start:
{
uint8_t v___x_2794_; 
v___x_2794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2792_, v_x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2792_ = stack[1].m_obj;
lean_object* v_x_2793_ = stack[2].m_obj;
uint8_t v_res_2795_;
v_res_2795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_box(0), v_a_2792_, v_x_2793_);
stack->m_num = v_res_2795_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2796_, lean_object* v_a_2797_, lean_object* v_x_2798_){
_start:
{
uint8_t v_res_2799_; lean_object* v_r_2800_; 
v_res_2799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_2796_, v_a_2797_, v_x_2798_);
lean_dec(v_x_2798_);
lean_dec_ref(v_a_2797_);
v_r_2800_ = lean_box(v_res_2799_);
return v_r_2800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_2801_, lean_object* v_data_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_data_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_2804_, lean_object* v_a_2805_, lean_object* v_b_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2805_, v_b_2806_, v_x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_2809_, lean_object* v_i_2810_, lean_object* v_source_2811_, lean_object* v_target_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_2810_, v_source_2811_, v_target_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_2815_, v_x_2816_);
return v___x_2817_;
}
}
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Meta_Sym_foldProjs(v_e_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_foldProjs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2818_ = stack[0].m_obj;
lean_object* v_a_2819_ = stack[1].m_obj;
lean_object* v_a_2820_ = stack[2].m_obj;
lean_object* v_a_2821_ = stack[3].m_obj;
lean_object* v_a_2822_ = stack[4].m_obj;
lean_object* v_res_2825_;
v_res_2825_ = l_Lean_Meta_Grind_foldProjs(v_e_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
stack->m_obj
 = v_res_2825_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Meta_Grind_foldProjs(v_e_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
return v_res_2832_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_normalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2833_ = stack[0].m_obj;
lean_object* v_config_2834_ = stack[1].m_obj;
lean_object* v_a_2835_ = stack[2].m_obj;
lean_object* v_a_2836_ = stack[3].m_obj;
lean_object* v_a_2837_ = stack[4].m_obj;
lean_object* v_a_2838_ = stack[5].m_obj;
lean_object* v_res_2840_;
v_res_2840_ = lean_grind_normalize(v_e_2833_, v_config_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_);
stack->m_obj
 = v_res_2840_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_2841_, lean_object* v_config_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_00___x40___internal___hyg_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = lean_grind_normalize(v_e_2841_, v_config_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
return v_res_2848_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = lean_box(0);
v___x_2857_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2858_ = l_Lean_mkConst(v___x_2857_, v___x_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_2861_ = l_Lean_Expr_app___override(v___x_2860_, v_e_2859_);
return v___x_2861_;
}
}
uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_2862_){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2864_ = lean_unsigned_to_nat(1u);
v___x_2865_ = l_Lean_Expr_isAppOfArity(v_e_2862_, v___x_2863_, v___x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isMatchCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2862_ = stack[0].m_obj;
uint8_t v_res_2866_;
v_res_2866_ = l_Lean_Meta_Grind_isMatchCond(v_e_2862_);
stack->m_num = v_res_2866_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_2867_){
_start:
{
uint8_t v_res_2868_; lean_object* v_r_2869_; 
v_res_2868_ = l_Lean_Meta_Grind_isMatchCond(v_e_2867_);
lean_dec_ref(v_e_2867_);
v_r_2869_ = lean_box(v_res_2868_);
return v_r_2869_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_box(0);
v___x_2876_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2877_ = l_Lean_mkConst(v___x_2876_, v___x_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_2878_){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_2880_ = l_Lean_Expr_app___override(v___x_2879_, v_e_2878_);
return v___x_2880_;
}
}
uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_2881_){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2882_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = l_Lean_Expr_isAppOfArity(v_e_2881_, v___x_2882_, v___x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isPreMatchCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2881_ = stack[0].m_obj;
uint8_t v_res_2885_;
v_res_2885_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_2881_);
stack->m_num = v_res_2885_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_2886_){
_start:
{
uint8_t v_res_2887_; lean_object* v_r_2888_; 
v_res_2887_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_2886_);
lean_dec_ref(v_e_2886_);
v_r_2888_ = lean_box(v_res_2887_);
return v_r_2888_;
}
}
lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___x_2897_; 
lean_inc_ref(v_e_2891_);
v___x_2897_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2891_, v_a_2892_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2911_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2911_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2911_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = l_Lean_Expr_cleanupAnnotations(v_a_2898_);
v___x_2903_ = l_Lean_Expr_isApp(v___x_2902_);
if (v___x_2903_ == 0)
{
lean_dec_ref(v___x_2902_);
lean_del_object(v___x_2900_);
lean_dec_ref(v_e_2891_);
goto v___jp_2894_;
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2904_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2902_);
v___x_2905_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2906_ = l_Lean_Expr_isConstOf(v___x_2904_, v___x_2905_);
lean_dec_ref(v___x_2904_);
if (v___x_2906_ == 0)
{
lean_del_object(v___x_2900_);
lean_dec_ref(v_e_2891_);
goto v___jp_2894_;
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_e_2891_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2907_);
v___x_2909_ = v___x_2900_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v_e_2891_);
v_a_2912_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2897_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2897_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
v___jp_2894_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0));
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_reducePreMatchCond___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2891_ = stack[0].m_obj;
lean_object* v_a_2892_ = stack[1].m_obj;
lean_object* v_res_2920_;
v_res_2920_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_2891_, v_a_2892_);
stack->m_obj
 = v_res_2920_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_2921_, v_a_2922_);
lean_dec(v_a_2922_);
return v_res_2924_;
}
}
lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_2925_, v_a_2930_);
return v___x_2934_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_reducePreMatchCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2925_ = stack[0].m_obj;
lean_object* v_a_2926_ = stack[1].m_obj;
lean_object* v_a_2927_ = stack[2].m_obj;
lean_object* v_a_2928_ = stack[3].m_obj;
lean_object* v_a_2929_ = stack[4].m_obj;
lean_object* v_a_2930_ = stack[5].m_obj;
lean_object* v_a_2931_ = stack[6].m_obj;
lean_object* v_a_2932_ = stack[7].m_obj;
lean_object* v_res_2935_;
v_res_2935_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
stack->m_obj
 = v_res_2935_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
return v_res_2945_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_2964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_2965_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_2966_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2963_, v___x_2964_, v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2967_;
v_res_2967_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
stack->m_obj
 = v_res_2967_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11____boxed(lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
return v_res_2969_;
}
}
lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v___x_2974_; uint8_t v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_2975_ = 0;
v___x_2976_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2970_, v___x_2974_, v___x_2975_, v_a_2971_, v_a_2972_);
return v___x_2976_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addPreMatchCondSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2970_ = stack[0].m_obj;
lean_object* v_a_2971_ = stack[1].m_obj;
lean_object* v_a_2972_ = stack[2].m_obj;
lean_object* v_res_2977_;
v_res_2977_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_2970_, v_a_2971_, v_a_2972_);
stack->m_obj
 = v_res_2977_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
return v_res_2982_;
}
}
lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2993_; uint8_t v___x_2994_; 
lean_inc_ref(v_e_2983_);
v___x_2993_ = l_Lean_Expr_cleanupAnnotations(v_e_2983_);
v___x_2994_ = l_Lean_Expr_isApp(v___x_2993_);
if (v___x_2994_ == 0)
{
lean_dec_ref(v___x_2993_);
goto v___jp_2989_;
}
else
{
lean_object* v_arg_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v_arg_2995_ = lean_ctor_get(v___x_2993_, 1);
lean_inc_ref(v_arg_2995_);
v___x_2996_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2993_);
v___x_2997_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2998_ = l_Lean_Expr_isConstOf(v___x_2996_, v___x_2997_);
lean_dec_ref(v___x_2996_);
if (v___x_2998_ == 0)
{
lean_dec_ref(v_arg_2995_);
goto v___jp_2989_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_dec_ref(v_e_2983_);
v___x_2999_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_2995_);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
}
v___jp_2989_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_e_2983_);
v___x_2991_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_replacePreMatchCond___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2983_ = stack[0].m_obj;
lean_object* v___y_2984_ = stack[1].m_obj;
lean_object* v___y_2985_ = stack[2].m_obj;
lean_object* v___y_2986_ = stack[3].m_obj;
lean_object* v___y_2987_ = stack[4].m_obj;
lean_object* v_res_3003_;
v_res_3003_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
stack->m_obj
 = v_res_3003_;
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
lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_replacePreMatchCond___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3011_ = stack[0].m_obj;
lean_object* v___y_3012_ = stack[1].m_obj;
lean_object* v___y_3013_ = stack[2].m_obj;
lean_object* v___y_3014_ = stack[3].m_obj;
lean_object* v___y_3015_ = stack[4].m_obj;
lean_object* v_res_3019_;
v_res_3019_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
stack->m_obj
 = v_res_3019_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
return v_res_3026_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_object* v_00_u03b1_3027_, lean_object* v_x_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_apply_1(v_x_3028_, lean_box(0));
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3028_ = stack[1].m_obj;
lean_object* v___y_3029_ = stack[2].m_obj;
lean_object* v___y_3030_ = stack[3].m_obj;
lean_object* v___y_3031_ = stack[4].m_obj;
lean_object* v___y_3032_ = stack[5].m_obj;
lean_object* v_res_3036_;
v_res_3036_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v_x_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
stack->m_obj
 = v_res_3036_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(v_00_u03b1_3037_, v_x_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3044_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___y_3053_; uint8_t v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; uint8_t v___y_3067_; uint16_t v___y_3068_; lean_object* v_toCold_3073_; lean_object* v_currRecDepth_3074_; lean_object* v_ref_3075_; uint16_t v_optionFlags_3076_; uint8_t v_suppressElabErrors_3077_; uint8_t v_isRecordingDeps_3078_; lean_object* v_maxRecDepth_3079_; lean_object* v_cancelTk_x3f_3080_; 
v_toCold_3073_ = lean_ctor_get(v___y_3049_, 0);
v_currRecDepth_3074_ = lean_ctor_get(v___y_3049_, 1);
v_ref_3075_ = lean_ctor_get(v___y_3049_, 2);
v_optionFlags_3076_ = lean_ctor_get_uint16(v___y_3049_, sizeof(void*)*3);
v_suppressElabErrors_3077_ = lean_ctor_get_uint8(v___y_3049_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3078_ = lean_ctor_get_uint8(v___y_3049_, sizeof(void*)*3 + 3);
v_maxRecDepth_3079_ = lean_ctor_get(v_toCold_3073_, 3);
v_cancelTk_x3f_3080_ = lean_ctor_get(v_toCold_3073_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3080_) == 1)
{
lean_object* v_val_3086_; uint8_t v___x_3087_; 
v_val_3086_ = lean_ctor_get(v_cancelTk_x3f_3080_, 0);
v___x_3087_ = l_IO_CancelToken_isSet(v_val_3086_);
if (v___x_3087_ == 0)
{
goto v___jp_3081_;
}
else
{
lean_object* v___x_3088_; lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v_x_3045_);
v___x_3088_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
goto v___jp_3081_;
}
v___jp_3052_:
{
if (lean_obj_tag(v___y_3053_) == 0)
{
return v___y_3053_;
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v_a_3054_ = lean_ctor_get(v___y_3053_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___y_3053_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___y_3053_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___y_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
v___jp_3062_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = lean_unsigned_to_nat(1u);
v___x_3070_ = lean_nat_add(v___y_3064_, v___x_3069_);
lean_inc_ref(v___y_3066_);
v___x_3071_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3071_, 0, v___y_3066_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
lean_ctor_set(v___x_3071_, 2, v___y_3065_);
lean_ctor_set_uint16(v___x_3071_, sizeof(void*)*3, v___y_3068_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3 + 2, v___y_3067_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3 + 3, v___y_3063_);
lean_inc(v___y_3050_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3047_);
lean_inc(v___y_3046_);
v___x_3072_ = lean_apply_6(v_x_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___x_3071_, v___y_3050_, lean_box(0));
v___y_3053_ = v___x_3072_;
goto v___jp_3052_;
}
v___jp_3081_:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = lean_nat_dec_eq(v_maxRecDepth_3079_, v___x_3082_);
if (v___x_3083_ == 0)
{
uint8_t v___x_3084_; 
v___x_3084_ = lean_nat_dec_eq(v_currRecDepth_3074_, v_maxRecDepth_3079_);
if (v___x_3084_ == 0)
{
lean_inc(v_ref_3075_);
v___y_3063_ = v_isRecordingDeps_3078_;
v___y_3064_ = v_currRecDepth_3074_;
v___y_3065_ = v_ref_3075_;
v___y_3066_ = v_toCold_3073_;
v___y_3067_ = v_suppressElabErrors_3077_;
v___y_3068_ = v_optionFlags_3076_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3085_; 
lean_dec_ref(v_x_3045_);
lean_inc(v_ref_3075_);
v___x_3085_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_3075_);
v___y_3053_ = v___x_3085_;
goto v___jp_3052_;
}
}
else
{
lean_inc(v_ref_3075_);
v___y_3063_ = v_isRecordingDeps_3078_;
v___y_3064_ = v_currRecDepth_3074_;
v___y_3065_ = v_ref_3075_;
v___y_3066_ = v_toCold_3073_;
v___y_3067_ = v_suppressElabErrors_3077_;
v___y_3068_ = v_optionFlags_3076_;
goto v___jp_3062_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3045_ = stack[0].m_obj;
lean_object* v___y_3046_ = stack[1].m_obj;
lean_object* v___y_3047_ = stack[2].m_obj;
lean_object* v___y_3048_ = stack[3].m_obj;
lean_object* v___y_3049_ = stack[4].m_obj;
lean_object* v___y_3050_ = stack[5].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
stack->m_obj
 = v_res_3097_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
return v_res_3105_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_apply_1(v_x_3107_, lean_box(0));
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3107_ = stack[1].m_obj;
lean_object* v___y_3108_ = stack[2].m_obj;
lean_object* v___y_3109_ = stack[3].m_obj;
lean_object* v___y_3110_ = stack[4].m_obj;
lean_object* v___y_3111_ = stack[5].m_obj;
lean_object* v_res_3115_;
v_res_3115_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
stack->m_obj
 = v_res_3115_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_x_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(v_00_u03b1_3116_, v_x_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
return v_res_3123_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_3124_, lean_object* v_post_3125_, size_t v_sz_3126_, size_t v_i_3127_, lean_object* v_bs_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_usize_dec_lt(v_i_3127_, v_sz_3126_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_bs_3128_);
return v___x_3136_;
}
else
{
lean_object* v_v_3137_; lean_object* v___x_3138_; lean_object* v_bs_x27_3139_; lean_object* v___x_3140_; 
v_v_3137_ = lean_array_uget(v_bs_3128_, v_i_3127_);
v___x_3138_ = lean_unsigned_to_nat(0u);
v_bs_x27_3139_ = lean_array_uset(v_bs_3128_, v_i_3127_, v___x_3138_);
lean_inc_ref(v_post_3125_);
lean_inc_ref(v_pre_3124_);
v___x_3140_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3124_, v_post_3125_, v_v_3137_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3127_, v___x_3142_);
v___x_3144_ = lean_array_uset(v_bs_x27_3139_, v_i_3127_, v_a_3141_);
v_i_3127_ = v___x_3143_;
v_bs_3128_ = v___x_3144_;
goto _start;
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v_bs_x27_3139_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
v_a_3146_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3140_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3140_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3124_ = stack[0].m_obj;
lean_object* v_post_3125_ = stack[1].m_obj;
size_t v_sz_3126_ = stack[2].m_num;
size_t v_i_3127_ = stack[3].m_num;
lean_object* v_bs_3128_ = stack[4].m_obj;
lean_object* v___y_3129_ = stack[5].m_obj;
lean_object* v___y_3130_ = stack[6].m_obj;
lean_object* v___y_3131_ = stack[7].m_obj;
lean_object* v___y_3132_ = stack[8].m_obj;
lean_object* v___y_3133_ = stack[9].m_obj;
lean_object* v_res_3154_;
v_res_3154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3124_, v_post_3125_, v_sz_3126_, v_i_3127_, v_bs_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
stack->m_obj
 = v_res_3154_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_3155_, lean_object* v_post_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
if (lean_obj_tag(v_x_3157_) == 5)
{
lean_object* v_fn_3166_; lean_object* v_arg_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_fn_3166_ = lean_ctor_get(v_x_3157_, 0);
lean_inc_ref(v_fn_3166_);
v_arg_3167_ = lean_ctor_get(v_x_3157_, 1);
lean_inc_ref(v_arg_3167_);
lean_dec_ref_known(v_x_3157_, 2);
v___x_3168_ = lean_array_set(v_x_3158_, v_x_3159_, v_arg_3167_);
v___x_3169_ = lean_unsigned_to_nat(1u);
v___x_3170_ = lean_nat_sub(v_x_3159_, v___x_3169_);
lean_dec(v_x_3159_);
v_x_3157_ = v_fn_3166_;
v_x_3158_ = v___x_3168_;
v_x_3159_ = v___x_3170_;
goto _start;
}
else
{
lean_object* v___x_3172_; 
lean_dec(v_x_3159_);
lean_inc_ref(v_post_3156_);
lean_inc_ref(v_pre_3155_);
v___x_3172_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3155_, v_post_3156_, v_x_3157_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; size_t v_sz_3174_; size_t v___x_3175_; lean_object* v___x_3176_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v_sz_3174_ = lean_array_size(v_x_3158_);
v___x_3175_ = ((size_t)0ULL);
lean_inc_ref(v_post_3156_);
lean_inc_ref(v_pre_3155_);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3155_, v_post_3156_, v_sz_3174_, v___x_3175_, v_x_3158_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3178_ = l_Lean_mkAppN(v_a_3173_, v_a_3177_);
lean_dec(v_a_3177_);
v___x_3179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3155_, v_post_3156_, v___x_3178_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
return v___x_3179_;
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_a_3173_);
lean_dec_ref(v_post_3156_);
lean_dec_ref(v_pre_3155_);
v_a_3180_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3176_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3176_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_dec_ref(v_x_3158_);
lean_dec_ref(v_post_3156_);
lean_dec_ref(v_pre_3155_);
return v___x_3172_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3155_ = stack[0].m_obj;
lean_object* v_post_3156_ = stack[1].m_obj;
lean_object* v_x_3157_ = stack[2].m_obj;
lean_object* v_x_3158_ = stack[3].m_obj;
lean_object* v_x_3159_ = stack[4].m_obj;
lean_object* v___y_3160_ = stack[5].m_obj;
lean_object* v___y_3161_ = stack[6].m_obj;
lean_object* v___y_3162_ = stack[7].m_obj;
lean_object* v___y_3163_ = stack[8].m_obj;
lean_object* v___y_3164_ = stack[9].m_obj;
lean_object* v_res_3188_;
v_res_3188_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3155_, v_post_3156_, v_x_3157_, v_x_3158_, v_x_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
stack->m_obj
 = v_res_3188_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v___x_3189_, lean_object* v_pre_3190_, lean_object* v_e_3191_, lean_object* v_post_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_Core_checkSystem(v___x_3189_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v___x_3200_; 
lean_dec_ref_known(v___x_3199_, 1);
lean_inc_ref(v_pre_3190_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc_ref(v_e_3191_);
v___x_3200_ = lean_apply_6(v_pre_3190_, v_e_3191_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, lean_box(0));
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3316_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3316_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3316_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___y_3206_; 
switch(lean_obj_tag(v_a_3201_))
{
case 0:
{
lean_object* v_e_3306_; lean_object* v___x_3308_; 
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_e_3191_);
lean_dec_ref(v_pre_3190_);
v_e_3306_ = lean_ctor_get(v_a_3201_, 0);
lean_inc_ref(v_e_3306_);
lean_dec_ref_known(v_a_3201_, 1);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v_e_3306_);
v___x_3308_ = v___x_3203_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_e_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
case 1:
{
lean_object* v_e_3310_; lean_object* v___x_3311_; 
lean_del_object(v___x_3203_);
lean_dec_ref(v_e_3191_);
v_e_3310_ = lean_ctor_get(v_a_3201_, 0);
lean_inc_ref(v_e_3310_);
lean_dec_ref_known(v_a_3201_, 1);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3311_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_e_3310_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v_a_3312_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3313_;
}
else
{
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3311_;
}
}
default: 
{
lean_object* v_e_x3f_3314_; 
lean_del_object(v___x_3203_);
v_e_x3f_3314_ = lean_ctor_get(v_a_3201_, 0);
lean_inc(v_e_x3f_3314_);
lean_dec_ref_known(v_a_3201_, 1);
if (lean_obj_tag(v_e_x3f_3314_) == 0)
{
v___y_3206_ = v_e_3191_;
goto v___jp_3205_;
}
else
{
lean_object* v_val_3315_; 
lean_dec_ref(v_e_3191_);
v_val_3315_ = lean_ctor_get(v_e_x3f_3314_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v_e_x3f_3314_, 1);
v___y_3206_ = v_val_3315_;
goto v___jp_3205_;
}
}
}
v___jp_3205_:
{
switch(lean_obj_tag(v___y_3206_))
{
case 7:
{
lean_object* v_binderName_3207_; lean_object* v_binderType_3208_; lean_object* v_body_3209_; uint8_t v_binderInfo_3210_; lean_object* v___x_3211_; 
v_binderName_3207_ = lean_ctor_get(v___y_3206_, 0);
v_binderType_3208_ = lean_ctor_get(v___y_3206_, 1);
v_body_3209_ = lean_ctor_get(v___y_3206_, 2);
v_binderInfo_3210_ = lean_ctor_get_uint8(v___y_3206_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3208_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3211_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_binderType_3208_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
lean_inc_ref(v_body_3209_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3213_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_body_3209_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; size_t v___x_3215_; size_t v___x_3216_; uint8_t v___x_3217_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = lean_ptr_addr(v_binderType_3208_);
v___x_3216_ = lean_ptr_addr(v_a_3212_);
v___x_3217_ = lean_usize_dec_eq(v___x_3215_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_inc(v_binderName_3207_);
lean_dec_ref_known(v___y_3206_, 3);
v___x_3218_ = l_Lean_Expr_forallE___override(v_binderName_3207_, v_a_3212_, v_a_3214_, v_binderInfo_3210_);
v___x_3219_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3218_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3219_;
}
else
{
size_t v___x_3220_; size_t v___x_3221_; uint8_t v___x_3222_; 
v___x_3220_ = lean_ptr_addr(v_body_3209_);
v___x_3221_ = lean_ptr_addr(v_a_3214_);
v___x_3222_ = lean_usize_dec_eq(v___x_3220_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_inc(v_binderName_3207_);
lean_dec_ref_known(v___y_3206_, 3);
v___x_3223_ = l_Lean_Expr_forallE___override(v_binderName_3207_, v_a_3212_, v_a_3214_, v_binderInfo_3210_);
v___x_3224_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3223_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3224_;
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3210_, v_binderInfo_3210_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_inc(v_binderName_3207_);
lean_dec_ref_known(v___y_3206_, 3);
v___x_3226_ = l_Lean_Expr_forallE___override(v_binderName_3207_, v_a_3212_, v_a_3214_, v_binderInfo_3210_);
v___x_3227_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3226_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; 
lean_dec(v_a_3214_);
lean_dec(v_a_3212_);
v___x_3228_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___y_3206_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3228_;
}
}
}
}
else
{
lean_dec(v_a_3212_);
lean_dec_ref_known(v___y_3206_, 3);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3213_;
}
}
else
{
lean_dec_ref_known(v___y_3206_, 3);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3211_;
}
}
case 6:
{
lean_object* v_binderName_3229_; lean_object* v_binderType_3230_; lean_object* v_body_3231_; uint8_t v_binderInfo_3232_; lean_object* v___x_3233_; 
v_binderName_3229_ = lean_ctor_get(v___y_3206_, 0);
v_binderType_3230_ = lean_ctor_get(v___y_3206_, 1);
v_body_3231_ = lean_ctor_get(v___y_3206_, 2);
v_binderInfo_3232_ = lean_ctor_get_uint8(v___y_3206_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3230_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3233_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_binderType_3230_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
lean_inc_ref(v_body_3231_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3235_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_body_3231_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; size_t v___x_3237_; size_t v___x_3238_; uint8_t v___x_3239_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = lean_ptr_addr(v_binderType_3230_);
v___x_3238_ = lean_ptr_addr(v_a_3234_);
v___x_3239_ = lean_usize_dec_eq(v___x_3237_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_inc(v_binderName_3229_);
lean_dec_ref_known(v___y_3206_, 3);
v___x_3240_ = l_Lean_Expr_lam___override(v_binderName_3229_, v_a_3234_, v_a_3236_, v_binderInfo_3232_);
v___x_3241_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3240_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3241_;
}
else
{
size_t v___x_3242_; size_t v___x_3243_; uint8_t v___x_3244_; 
v___x_3242_ = lean_ptr_addr(v_body_3231_);
v___x_3243_ = lean_ptr_addr(v_a_3236_);
v___x_3244_ = lean_usize_dec_eq(v___x_3242_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_inc(v_binderName_3229_);
lean_dec_ref_known(v___y_3206_, 3);
v___x_3245_ = l_Lean_Expr_lam___override(v_binderName_3229_, v_a_3234_, v_a_3236_, v_binderInfo_3232_);
v___x_3246_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3245_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3246_;
}
else
{
uint8_t v___x_3247_; 
v___x_3247_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3232_, v_binderInfo_3232_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_inc(v_binderName_3229_);
lean_dec_ref_known(v___y_3206_, 3);
v___x_3248_ = l_Lean_Expr_lam___override(v_binderName_3229_, v_a_3234_, v_a_3236_, v_binderInfo_3232_);
v___x_3249_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3248_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; 
lean_dec(v_a_3236_);
lean_dec(v_a_3234_);
v___x_3250_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___y_3206_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3250_;
}
}
}
}
else
{
lean_dec(v_a_3234_);
lean_dec_ref_known(v___y_3206_, 3);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3235_;
}
}
else
{
lean_dec_ref_known(v___y_3206_, 3);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3233_;
}
}
case 8:
{
lean_object* v_declName_3251_; lean_object* v_type_3252_; lean_object* v_value_3253_; lean_object* v_body_3254_; uint8_t v_nondep_3255_; lean_object* v___x_3256_; 
v_declName_3251_ = lean_ctor_get(v___y_3206_, 0);
v_type_3252_ = lean_ctor_get(v___y_3206_, 1);
v_value_3253_ = lean_ctor_get(v___y_3206_, 2);
v_body_3254_ = lean_ctor_get(v___y_3206_, 3);
v_nondep_3255_ = lean_ctor_get_uint8(v___y_3206_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3252_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3256_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_type_3252_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
lean_inc_ref(v_value_3253_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3258_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_value_3253_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3260_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
lean_inc_ref(v_body_3254_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3260_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_body_3254_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; size_t v___x_3262_; size_t v___x_3263_; uint8_t v___x_3264_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___x_3262_ = lean_ptr_addr(v_type_3252_);
v___x_3263_ = lean_ptr_addr(v_a_3257_);
v___x_3264_ = lean_usize_dec_eq(v___x_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_inc(v_declName_3251_);
lean_dec_ref_known(v___y_3206_, 4);
v___x_3265_ = l_Lean_Expr_letE___override(v_declName_3251_, v_a_3257_, v_a_3259_, v_a_3261_, v_nondep_3255_);
v___x_3266_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3265_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3266_;
}
else
{
size_t v___x_3267_; size_t v___x_3268_; uint8_t v___x_3269_; 
v___x_3267_ = lean_ptr_addr(v_value_3253_);
v___x_3268_ = lean_ptr_addr(v_a_3259_);
v___x_3269_ = lean_usize_dec_eq(v___x_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_inc(v_declName_3251_);
lean_dec_ref_known(v___y_3206_, 4);
v___x_3270_ = l_Lean_Expr_letE___override(v_declName_3251_, v_a_3257_, v_a_3259_, v_a_3261_, v_nondep_3255_);
v___x_3271_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3270_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3271_;
}
else
{
size_t v___x_3272_; size_t v___x_3273_; uint8_t v___x_3274_; 
v___x_3272_ = lean_ptr_addr(v_body_3254_);
v___x_3273_ = lean_ptr_addr(v_a_3261_);
v___x_3274_ = lean_usize_dec_eq(v___x_3272_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_inc(v_declName_3251_);
lean_dec_ref_known(v___y_3206_, 4);
v___x_3275_ = l_Lean_Expr_letE___override(v_declName_3251_, v_a_3257_, v_a_3259_, v_a_3261_, v_nondep_3255_);
v___x_3276_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3275_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3276_;
}
else
{
lean_object* v___x_3277_; 
lean_dec(v_a_3261_);
lean_dec(v_a_3259_);
lean_dec(v_a_3257_);
v___x_3277_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___y_3206_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3277_;
}
}
}
}
else
{
lean_dec(v_a_3259_);
lean_dec(v_a_3257_);
lean_dec_ref_known(v___y_3206_, 4);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3260_;
}
}
else
{
lean_dec(v_a_3257_);
lean_dec_ref_known(v___y_3206_, 4);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3258_;
}
}
else
{
lean_dec_ref_known(v___y_3206_, 4);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3256_;
}
}
case 5:
{
lean_object* v_dummy_3278_; lean_object* v_nargs_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_dummy_3278_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3279_ = l_Lean_Expr_getAppNumArgs(v___y_3206_);
lean_inc(v_nargs_3279_);
v___x_3280_ = lean_mk_array(v_nargs_3279_, v_dummy_3278_);
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = lean_nat_sub(v_nargs_3279_, v___x_3281_);
lean_dec(v_nargs_3279_);
v___x_3283_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3190_, v_post_3192_, v___y_3206_, v___x_3280_, v___x_3282_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3283_;
}
case 10:
{
lean_object* v_data_3284_; lean_object* v_expr_3285_; lean_object* v___x_3286_; 
v_data_3284_ = lean_ctor_get(v___y_3206_, 0);
v_expr_3285_ = lean_ctor_get(v___y_3206_, 1);
lean_inc_ref(v_expr_3285_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3286_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_expr_3285_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; size_t v___x_3288_; size_t v___x_3289_; uint8_t v___x_3290_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = lean_ptr_addr(v_expr_3285_);
v___x_3289_ = lean_ptr_addr(v_a_3287_);
v___x_3290_ = lean_usize_dec_eq(v___x_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_inc(v_data_3284_);
lean_dec_ref_known(v___y_3206_, 2);
v___x_3291_ = l_Lean_Expr_mdata___override(v_data_3284_, v_a_3287_);
v___x_3292_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3291_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3292_;
}
else
{
lean_object* v___x_3293_; 
lean_dec(v_a_3287_);
v___x_3293_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___y_3206_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3293_;
}
}
else
{
lean_dec_ref_known(v___y_3206_, 2);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3286_;
}
}
case 11:
{
lean_object* v_typeName_3294_; lean_object* v_idx_3295_; lean_object* v_struct_3296_; lean_object* v___x_3297_; 
v_typeName_3294_ = lean_ctor_get(v___y_3206_, 0);
v_idx_3295_ = lean_ctor_get(v___y_3206_, 1);
v_struct_3296_ = lean_ctor_get(v___y_3206_, 2);
lean_inc_ref(v_struct_3296_);
lean_inc_ref(v_post_3192_);
lean_inc_ref(v_pre_3190_);
v___x_3297_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3190_, v_post_3192_, v_struct_3296_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; size_t v___x_3299_; size_t v___x_3300_; uint8_t v___x_3301_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = lean_ptr_addr(v_struct_3296_);
v___x_3300_ = lean_ptr_addr(v_a_3298_);
v___x_3301_ = lean_usize_dec_eq(v___x_3299_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_inc(v_idx_3295_);
lean_inc(v_typeName_3294_);
lean_dec_ref_known(v___y_3206_, 3);
v___x_3302_ = l_Lean_Expr_proj___override(v_typeName_3294_, v_idx_3295_, v_a_3298_);
v___x_3303_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___x_3302_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3303_;
}
else
{
lean_object* v___x_3304_; 
lean_dec(v_a_3298_);
v___x_3304_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___y_3206_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3304_;
}
}
else
{
lean_dec_ref_known(v___y_3206_, 3);
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_pre_3190_);
return v___x_3297_;
}
}
default: 
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3190_, v_post_3192_, v___y_3206_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
return v___x_3305_;
}
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_e_3191_);
lean_dec_ref(v_pre_3190_);
v_a_3317_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3200_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3200_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref(v_post_3192_);
lean_dec_ref(v_e_3191_);
lean_dec_ref(v_pre_3190_);
v_a_3325_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3199_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3199_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3189_ = stack[0].m_obj;
lean_object* v_pre_3190_ = stack[1].m_obj;
lean_object* v_e_3191_ = stack[2].m_obj;
lean_object* v_post_3192_ = stack[3].m_obj;
lean_object* v___y_3193_ = stack[4].m_obj;
lean_object* v___y_3194_ = stack[5].m_obj;
lean_object* v___y_3195_ = stack[6].m_obj;
lean_object* v___y_3196_ = stack[7].m_obj;
lean_object* v___y_3197_ = stack[8].m_obj;
lean_object* v_res_3333_;
v_res_3333_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_3189_, v_pre_3190_, v_e_3191_, v_post_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
stack->m_obj
 = v_res_3333_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v___x_3334_, lean_object* v_pre_3335_, lean_object* v_e_3336_, lean_object* v_post_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_3334_, v_pre_3335_, v_e_3336_, v_post_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
return v_res_3344_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_3345_, lean_object* v_post_3346_, lean_object* v_e_3347_, lean_object* v_a_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_inc(v_a_3348_);
v___x_3354_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3354_, 0, lean_box(0));
lean_closure_set(v___x_3354_, 1, lean_box(0));
lean_closure_set(v___x_3354_, 2, v_a_3348_);
v___x_3355_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___x_3354_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3387_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3387_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3387_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3356_, v_e_3347_);
lean_dec(v_a_3356_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; lean_object* v___f_3362_; lean_object* v___x_3363_; 
lean_del_object(v___x_3358_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_3347_);
v___f_3362_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3362_, 0, v___x_3361_);
lean_closure_set(v___f_3362_, 1, v_pre_3345_);
lean_closure_set(v___f_3362_, 2, v_e_3347_);
lean_closure_set(v___f_3362_, 3, v_post_3346_);
v___x_3363_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_3362_, v_a_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc_n(v_a_3364_, 2);
lean_dec_ref_known(v___x_3363_, 1);
lean_inc(v_a_3348_);
v___f_3365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3365_, 0, v_a_3348_);
lean_closure_set(v___f_3365_, 1, v_e_3347_);
lean_closure_set(v___f_3365_, 2, v_a_3364_);
v___x_3366_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___f_3365_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3373_ == 0)
{
lean_object* v_unused_3374_; 
v_unused_3374_ = lean_ctor_get(v___x_3366_, 0);
lean_dec(v_unused_3374_);
v___x_3368_ = v___x_3366_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_dec(v___x_3366_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v_a_3364_);
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3364_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_a_3364_);
v_a_3375_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3366_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3366_);
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
else
{
lean_dec_ref(v_e_3347_);
return v___x_3363_;
}
}
else
{
lean_object* v_val_3383_; lean_object* v___x_3385_; 
lean_dec_ref(v_e_3347_);
lean_dec_ref(v_post_3346_);
lean_dec_ref(v_pre_3345_);
v_val_3383_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_val_3383_);
lean_dec_ref_known(v___x_3360_, 1);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v_val_3383_);
v___x_3385_ = v___x_3358_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_val_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v_e_3347_);
lean_dec_ref(v_post_3346_);
lean_dec_ref(v_pre_3345_);
v_a_3388_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3355_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3355_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3345_ = stack[0].m_obj;
lean_object* v_post_3346_ = stack[1].m_obj;
lean_object* v_e_3347_ = stack[2].m_obj;
lean_object* v_a_3348_ = stack[3].m_obj;
lean_object* v___y_3349_ = stack[4].m_obj;
lean_object* v___y_3350_ = stack[5].m_obj;
lean_object* v___y_3351_ = stack[6].m_obj;
lean_object* v___y_3352_ = stack[7].m_obj;
lean_object* v_res_3396_;
v_res_3396_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3345_, v_post_3346_, v_e_3347_, v_a_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
stack->m_obj
 = v_res_3396_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_3397_, lean_object* v_post_3398_, lean_object* v_e_3399_, lean_object* v_a_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; 
lean_inc_ref(v_post_3398_);
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3403_);
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3401_);
lean_inc_ref(v_e_3399_);
v___x_3406_ = lean_apply_6(v_post_3398_, v_e_3399_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, lean_box(0));
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3425_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3425_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3425_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
switch(lean_obj_tag(v_a_3407_))
{
case 0:
{
lean_object* v_e_3411_; lean_object* v___x_3413_; 
lean_dec_ref(v_e_3399_);
lean_dec_ref(v_post_3398_);
lean_dec_ref(v_pre_3397_);
v_e_3411_ = lean_ctor_get(v_a_3407_, 0);
lean_inc_ref(v_e_3411_);
lean_dec_ref_known(v_a_3407_, 1);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_e_3411_);
v___x_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_e_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
case 1:
{
lean_object* v_e_3415_; lean_object* v___x_3416_; 
lean_del_object(v___x_3409_);
lean_dec_ref(v_e_3399_);
v_e_3415_ = lean_ctor_get(v_a_3407_, 0);
lean_inc_ref(v_e_3415_);
lean_dec_ref_known(v_a_3407_, 1);
v___x_3416_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3397_, v_post_3398_, v_e_3415_, v_a_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
return v___x_3416_;
}
default: 
{
lean_object* v_e_x3f_3417_; 
lean_dec_ref(v_post_3398_);
lean_dec_ref(v_pre_3397_);
v_e_x3f_3417_ = lean_ctor_get(v_a_3407_, 0);
lean_inc(v_e_x3f_3417_);
lean_dec_ref_known(v_a_3407_, 1);
if (lean_obj_tag(v_e_x3f_3417_) == 0)
{
lean_object* v___x_3419_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_e_3399_);
v___x_3419_ = v___x_3409_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_e_3399_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
else
{
lean_object* v_val_3421_; lean_object* v___x_3423_; 
lean_dec_ref(v_e_3399_);
v_val_3421_ = lean_ctor_get(v_e_x3f_3417_, 0);
lean_inc(v_val_3421_);
lean_dec_ref_known(v_e_x3f_3417_, 1);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_val_3421_);
v___x_3423_ = v___x_3409_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_val_3421_);
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
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v_e_3399_);
lean_dec_ref(v_post_3398_);
lean_dec_ref(v_pre_3397_);
v_a_3426_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3406_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3406_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3397_ = stack[0].m_obj;
lean_object* v_post_3398_ = stack[1].m_obj;
lean_object* v_e_3399_ = stack[2].m_obj;
lean_object* v_a_3400_ = stack[3].m_obj;
lean_object* v___y_3401_ = stack[4].m_obj;
lean_object* v___y_3402_ = stack[5].m_obj;
lean_object* v___y_3403_ = stack[6].m_obj;
lean_object* v___y_3404_ = stack[7].m_obj;
lean_object* v_res_3434_;
v_res_3434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3397_, v_post_3398_, v_e_3399_, v_a_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
stack->m_obj
 = v_res_3434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_3435_, lean_object* v_post_3436_, lean_object* v_e_3437_, lean_object* v_a_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3435_, v_post_3436_, v_e_3437_, v_a_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v_a_3438_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_3445_, lean_object* v_post_3446_, lean_object* v_sz_3447_, lean_object* v_i_3448_, lean_object* v_bs_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
size_t v_sz_boxed_3456_; size_t v_i_boxed_3457_; lean_object* v_res_3458_; 
v_sz_boxed_3456_ = lean_unbox_usize(v_sz_3447_);
lean_dec(v_sz_3447_);
v_i_boxed_3457_ = lean_unbox_usize(v_i_3448_);
lean_dec(v_i_3448_);
v_res_3458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3445_, v_post_3446_, v_sz_boxed_3456_, v_i_boxed_3457_, v_bs_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_3459_, lean_object* v_post_3460_, lean_object* v_x_3461_, lean_object* v_x_3462_, lean_object* v_x_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3459_, v_post_3460_, v_x_3461_, v_x_3462_, v_x_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_3471_, lean_object* v_post_3472_, lean_object* v_e_3473_, lean_object* v_a_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3471_, v_post_3472_, v_e_3473_, v_a_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v_a_3474_);
return v_res_3480_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_3481_, lean_object* v_pre_3482_, lean_object* v_post_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v_a_3491_; lean_object* v___x_3492_; 
v___x_3489_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_3490_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3489_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref(v___x_3490_);
v___x_3492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3482_, v_post_3483_, v_input_3481_, v_a_3491_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3494_, 0, lean_box(0));
lean_closure_set(v___x_3494_, 1, lean_box(0));
lean_closure_set(v___x_3494_, 2, v_a_3491_);
v___x_3495_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3494_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v___x_3495_, 0);
lean_dec(v_unused_3503_);
v___x_3497_ = v___x_3495_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_dec(v___x_3495_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_a_3493_);
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3493_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
else
{
lean_dec(v_a_3491_);
return v___x_3492_;
}
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_3481_ = stack[0].m_obj;
lean_object* v_pre_3482_ = stack[1].m_obj;
lean_object* v_post_3483_ = stack[2].m_obj;
lean_object* v___y_3484_ = stack[3].m_obj;
lean_object* v___y_3485_ = stack[4].m_obj;
lean_object* v___y_3486_ = stack[5].m_obj;
lean_object* v___y_3487_ = stack[6].m_obj;
lean_object* v_res_3504_;
v_res_3504_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_3481_, v_pre_3482_, v_post_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
stack->m_obj
 = v_res_3504_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_3505_, lean_object* v_pre_3506_, lean_object* v_post_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_3505_, v_pre_3506_, v_post_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3513_;
}
}
lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_3524_ = lean_find_expr(v___x_3523_, v_e_3517_);
if (lean_obj_tag(v___x_3524_) == 0)
{
uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = 1;
v___x_3526_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3526_, 0, v_e_3517_);
lean_ctor_set(v___x_3526_, 1, v___x_3524_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
return v___x_3527_;
}
else
{
lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3576_; 
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; 
v_unused_3577_ = lean_ctor_get(v___x_3524_, 0);
lean_dec(v_unused_3577_);
v___x_3529_ = v___x_3524_;
v_isShared_3530_ = v_isSharedCheck_3576_;
goto v_resetjp_3528_;
}
else
{
lean_dec(v___x_3524_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3576_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_pre_3531_; lean_object* v___f_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; 
v_pre_3531_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_3532_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
v___x_3533_ = 1;
lean_inc_ref(v_e_3517_);
v___x_3534_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_3517_, v_pre_3531_, v___f_3532_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc_n(v_a_3535_, 2);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = l_Lean_Meta_mkEqRefl(v_a_3535_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
lean_inc(v_a_3535_);
v___x_3538_ = l_Lean_Meta_mkEq(v_e_3517_, v_a_3535_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3551_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3551_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3551_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = l_Lean_Meta_mkExpectedPropHint(v_a_3537_, v_a_3539_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3543_);
v___x_3545_ = v___x_3529_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3546_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3546_, 0, v_a_3535_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
lean_ctor_set_uint8(v___x_3546_, sizeof(void*)*2, v___x_3533_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3546_);
v___x_3548_ = v___x_3541_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec(v_a_3537_);
lean_dec(v_a_3535_);
lean_del_object(v___x_3529_);
v_a_3552_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3538_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3538_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec(v_a_3535_);
lean_del_object(v___x_3529_);
lean_dec_ref(v_e_3517_);
v_a_3560_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3536_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3536_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_del_object(v___x_3529_);
lean_dec_ref(v_e_3517_);
v_a_3568_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3534_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3534_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_replacePreMatchCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3517_ = stack[0].m_obj;
lean_object* v_a_3518_ = stack[1].m_obj;
lean_object* v_a_3519_ = stack[2].m_obj;
lean_object* v_a_3520_ = stack[3].m_obj;
lean_object* v_a_3521_ = stack[4].m_obj;
lean_object* v_res_3578_;
v_res_3578_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
stack->m_obj
 = v_res_3578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
return v_res_3585_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3586_, lean_object* v_x_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3587_ = stack[1].m_obj;
lean_object* v___y_3588_ = stack[2].m_obj;
lean_object* v___y_3589_ = stack[3].m_obj;
lean_object* v___y_3590_ = stack[4].m_obj;
lean_object* v___y_3591_ = stack[5].m_obj;
lean_object* v___y_3592_ = stack[6].m_obj;
lean_object* v_res_3595_;
v_res_3595_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_box(0), v_x_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
stack->m_obj
 = v_res_3595_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3596_, lean_object* v_x_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_3596_, v_x_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
return v_res_3604_;
}
}
uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_3608_){
_start:
{
lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3609_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_3610_ = l_Lean_Expr_isAppOf(v_e_3608_, v___x_3609_);
if (v___x_3610_ == 0)
{
return v___x_3610_;
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3611_ = lean_unsigned_to_nat(5u);
v___x_3612_ = l_Lean_Expr_getAppNumArgs(v_e_3608_);
v___x_3613_ = lean_nat_dec_le(v___x_3611_, v___x_3612_);
lean_dec(v___x_3612_);
return v___x_3613_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3608_ = stack[0].m_obj;
uint8_t v_res_3614_;
v_res_3614_ = l_Lean_Meta_Grind_isIte(v_e_3608_);
stack->m_num = v_res_3614_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_3615_){
_start:
{
uint8_t v_res_3616_; lean_object* v_r_3617_; 
v_res_3616_ = l_Lean_Meta_Grind_isIte(v_e_3615_);
lean_dec_ref(v_e_3615_);
v_r_3617_ = lean_box(v_res_3616_);
return v_r_3617_;
}
}
uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_3621_){
_start:
{
lean_object* v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_3623_ = l_Lean_Expr_isAppOf(v_e_3621_, v___x_3622_);
if (v___x_3623_ == 0)
{
return v___x_3623_;
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v___x_3624_ = lean_unsigned_to_nat(5u);
v___x_3625_ = l_Lean_Expr_getAppNumArgs(v_e_3621_);
v___x_3626_ = lean_nat_dec_le(v___x_3624_, v___x_3625_);
lean_dec(v___x_3625_);
return v___x_3626_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isDIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3621_ = stack[0].m_obj;
uint8_t v_res_3627_;
v_res_3627_ = l_Lean_Meta_Grind_isDIte(v_e_3621_);
stack->m_num = v_res_3627_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_3628_){
_start:
{
uint8_t v_res_3629_; lean_object* v_r_3630_; 
v_res_3629_ = l_Lean_Meta_Grind_isDIte(v_e_3628_);
lean_dec_ref(v_e_3628_);
v_r_3630_ = lean_box(v_res_3629_);
return v_r_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_3631_){
_start:
{
uint8_t v___x_3632_; 
v___x_3632_ = l_Lean_Expr_isApp(v_e_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_box(0);
return v___x_3633_;
}
else
{
lean_object* v_f_3634_; uint8_t v___x_3635_; 
v_f_3634_ = l_Lean_Expr_appFn_x21(v_e_3631_);
v___x_3635_ = l_Lean_Expr_isApp(v_f_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
lean_dec_ref(v_f_3634_);
v___x_3636_ = lean_box(0);
return v___x_3636_;
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = l_Lean_Expr_appFn_x21(v_f_3634_);
lean_dec_ref(v_f_3634_);
v___x_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
return v___x_3638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Meta_Grind_getBinOp(v_e_3639_);
lean_dec_ref(v_e_3639_);
return v_res_3640_;
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
