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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_eraseIrrelevantMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_eraseIrrelevantMData___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_eraseIrrelevantMData___closed__0 = (const lean_object*)&l_Lean_MVarId_eraseIrrelevantMData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "reducePreMatchCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsMatchCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(150, 224, 247, 141, 87, 215, 99, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11____boxed(lean_object*);
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
v___x_91_ = l_instMonadEIO___redArg();
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
v___x_221_ = lean_unsigned_to_nat(649u);
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
lean_object* v_cs_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_317_; 
v_cs_304_ = lean_ctor_get(v_x_297_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_317_ == 0)
{
v___x_306_ = v_x_297_;
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_cs_304_);
lean_dec(v_x_297_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_317_;
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
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
lean_del_object(v___x_306_);
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_309_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_296_, v_cs_304_, v___x_314_, v___x_315_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec_ref(v_cs_304_);
return v___x_316_;
}
}
}
else
{
lean_object* v_vs_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_331_; 
v_vs_318_ = lean_ctor_get(v_x_297_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_331_ == 0)
{
v___x_320_ = v_x_297_;
v_isShared_321_ = v_isSharedCheck_331_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_vs_318_);
lean_dec(v_x_297_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_331_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_array_get_size(v_vs_318_);
v___x_324_ = lean_nat_dec_lt(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v_vs_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 0);
lean_ctor_set(v___x_320_, 0, v_x_298_);
v___x_326_ = v___x_320_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_x_298_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
lean_del_object(v___x_320_);
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_323_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_296_, v_vs_318_, v___x_328_, v___x_329_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec_ref(v_vs_318_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_auxDeclToFullName_332_, lean_object* v_as_333_, size_t v_i_334_, size_t v_stop_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_eq(v_i_334_, v_stop_335_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_array_uget_borrowed(v_as_333_, v_i_334_);
lean_inc(v___x_343_);
v___x_344_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_332_, v___x_343_, v_b_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; size_t v___x_346_; size_t v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_334_, v___x_346_);
v_i_334_ = v___x_347_;
v_b_336_ = v_a_345_;
goto _start;
}
else
{
return v___x_344_;
}
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v_b_336_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_auxDeclToFullName_350_, lean_object* v_as_351_, lean_object* v_i_352_, lean_object* v_stop_353_, lean_object* v_b_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
size_t v_i_boxed_360_; size_t v_stop_boxed_361_; lean_object* v_res_362_; 
v_i_boxed_360_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_stop_boxed_361_ = lean_unbox_usize(v_stop_353_);
lean_dec(v_stop_353_);
v_res_362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_350_, v_as_351_, v_i_boxed_360_, v_stop_boxed_361_, v_b_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec_ref(v_as_351_);
lean_dec(v_auxDeclToFullName_350_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_auxDeclToFullName_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_363_, v_x_364_, v_x_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v_auxDeclToFullName_363_);
return v_res_371_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(lean_object* v_auxDeclToFullName_373_, lean_object* v_x_374_, size_t v_x_375_, size_t v_x_376_, lean_object* v_x_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v_cs_383_; lean_object* v___x_384_; size_t v___x_385_; lean_object* v_j_386_; lean_object* v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v_cs_383_ = lean_ctor_get(v_x_374_, 0);
lean_inc_ref(v_cs_383_);
lean_dec_ref_known(v_x_374_, 1);
v___x_384_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0);
v___x_385_ = lean_usize_shift_right(v_x_375_, v_x_376_);
v_j_386_ = lean_usize_to_nat(v___x_385_);
v___x_387_ = lean_array_get_borrowed(v___x_384_, v_cs_383_, v_j_386_);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_shift_left(v___x_388_, v_x_376_);
v___x_390_ = lean_usize_sub(v___x_389_, v___x_388_);
v___x_391_ = lean_usize_land(v_x_375_, v___x_390_);
v___x_392_ = ((size_t)5ULL);
v___x_393_ = lean_usize_sub(v_x_376_, v___x_392_);
lean_inc(v___x_387_);
v___x_394_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_373_, v___x_387_, v___x_391_, v___x_393_, v_x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_j_386_, v___x_396_);
lean_dec(v_j_386_);
v___x_398_ = lean_array_get_size(v_cs_383_);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec(v___x_397_);
lean_dec_ref(v_cs_383_);
return v___x_394_;
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_400_ = lean_usize_of_nat(v___x_397_);
lean_dec(v___x_397_);
v___x_401_ = lean_usize_of_nat(v___x_398_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_373_, v_cs_383_, v___x_400_, v___x_401_, v_a_395_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec_ref(v_cs_383_);
return v___x_402_;
}
}
else
{
lean_dec(v_j_386_);
lean_dec_ref(v_cs_383_);
return v___x_394_;
}
}
else
{
lean_object* v_vs_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_416_; 
v_vs_403_ = lean_ctor_get(v_x_374_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_416_ == 0)
{
v___x_405_ = v_x_374_;
v_isShared_406_ = v_isSharedCheck_416_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_vs_403_);
lean_dec(v_x_374_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_416_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_usize_to_nat(v_x_375_);
v___x_408_ = lean_array_get_size(v_vs_403_);
v___x_409_ = lean_nat_dec_lt(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v___x_407_);
lean_dec_ref(v_vs_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 0);
lean_ctor_set(v___x_405_, 0, v_x_377_);
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_x_377_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
else
{
size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
lean_del_object(v___x_405_);
v___x_413_ = lean_usize_of_nat(v___x_407_);
lean_dec(v___x_407_);
v___x_414_ = lean_usize_of_nat(v___x_408_);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_373_, v_vs_403_, v___x_413_, v___x_414_, v_x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec_ref(v_vs_403_);
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_auxDeclToFullName_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
size_t v_x_4060__boxed_427_; size_t v_x_4061__boxed_428_; lean_object* v_res_429_; 
v_x_4060__boxed_427_ = lean_unbox_usize(v_x_419_);
lean_dec(v_x_419_);
v_x_4061__boxed_428_ = lean_unbox_usize(v_x_420_);
lean_dec(v_x_420_);
v_res_429_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_417_, v_x_418_, v_x_4060__boxed_427_, v_x_4061__boxed_428_, v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_auxDeclToFullName_417_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(lean_object* v_auxDeclToFullName_430_, lean_object* v_t_431_, lean_object* v_init_432_, lean_object* v_start_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_nat_dec_eq(v_start_433_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v_root_441_; lean_object* v_tail_442_; size_t v_shift_443_; lean_object* v_tailOff_444_; uint8_t v___x_445_; 
v_root_441_ = lean_ctor_get(v_t_431_, 0);
lean_inc_ref(v_root_441_);
v_tail_442_ = lean_ctor_get(v_t_431_, 1);
lean_inc_ref(v_tail_442_);
v_shift_443_ = lean_ctor_get_usize(v_t_431_, 4);
v_tailOff_444_ = lean_ctor_get(v_t_431_, 3);
lean_inc(v_tailOff_444_);
lean_dec_ref(v_t_431_);
v___x_445_ = lean_nat_dec_le(v_tailOff_444_, v_start_433_);
if (v___x_445_ == 0)
{
size_t v___x_446_; lean_object* v___x_447_; 
lean_dec(v_tailOff_444_);
v___x_446_ = lean_usize_of_nat(v_start_433_);
v___x_447_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_430_, v_root_441_, v___x_446_, v_shift_443_, v_init_432_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v___x_449_ = lean_array_get_size(v_tail_442_);
v___x_450_ = lean_nat_dec_lt(v___x_439_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec_ref(v_tail_442_);
return v___x_447_;
}
else
{
size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; 
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_451_ = ((size_t)0ULL);
v___x_452_ = lean_usize_of_nat(v___x_449_);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_430_, v_tail_442_, v___x_451_, v___x_452_, v_a_448_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec_ref(v_tail_442_);
return v___x_453_;
}
}
else
{
lean_dec_ref(v_tail_442_);
return v___x_447_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
lean_dec_ref(v_root_441_);
v___x_454_ = lean_nat_sub(v_start_433_, v_tailOff_444_);
lean_dec(v_tailOff_444_);
v___x_455_ = lean_array_get_size(v_tail_442_);
v___x_456_ = lean_nat_dec_lt(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v___x_454_);
lean_dec_ref(v_tail_442_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_init_432_);
return v___x_457_;
}
else
{
size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_usize_of_nat(v___x_454_);
lean_dec(v___x_454_);
v___x_459_ = lean_usize_of_nat(v___x_455_);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_430_, v_tail_442_, v___x_458_, v___x_459_, v_init_432_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec_ref(v_tail_442_);
return v___x_460_;
}
}
}
else
{
lean_object* v_root_461_; lean_object* v_tail_462_; lean_object* v___x_463_; 
v_root_461_ = lean_ctor_get(v_t_431_, 0);
lean_inc_ref(v_root_461_);
v_tail_462_ = lean_ctor_get(v_t_431_, 1);
lean_inc_ref(v_tail_462_);
lean_dec_ref(v_t_431_);
v___x_463_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_430_, v_root_461_, v_init_432_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v___x_465_ = lean_array_get_size(v_tail_462_);
v___x_466_ = lean_nat_dec_lt(v___x_439_, v___x_465_);
if (v___x_466_ == 0)
{
lean_dec_ref(v_tail_462_);
return v___x_463_;
}
else
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_467_ = ((size_t)0ULL);
v___x_468_ = lean_usize_of_nat(v___x_465_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_430_, v_tail_462_, v___x_467_, v___x_468_, v_a_464_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec_ref(v_tail_462_);
return v___x_469_;
}
}
else
{
lean_dec_ref(v_tail_462_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3___boxed(lean_object* v_auxDeclToFullName_470_, lean_object* v_t_471_, lean_object* v_init_472_, lean_object* v_start_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_470_, v_t_471_, v_init_472_, v_start_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v_start_473_);
lean_dec(v_auxDeclToFullName_470_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(lean_object* v_auxDeclToFullName_480_, lean_object* v_lctx_481_, lean_object* v_init_482_, lean_object* v_start_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_decls_489_; lean_object* v___x_490_; 
v_decls_489_ = lean_ctor_get(v_lctx_481_, 1);
lean_inc_ref(v_decls_489_);
lean_dec_ref(v_lctx_481_);
v___x_490_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_480_, v_decls_489_, v_init_482_, v_start_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2___boxed(lean_object* v_auxDeclToFullName_491_, lean_object* v_lctx_492_, lean_object* v_init_493_, lean_object* v_start_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_491_, v_lctx_492_, v_init_493_, v_start_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v_start_494_);
lean_dec(v_auxDeclToFullName_491_);
return v_res_500_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_501_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_unsigned_to_nat(32u);
v___x_505_ = lean_mk_empty_array_with_capacity(v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3(void){
_start:
{
size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_507_ = ((size_t)5ULL);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_unsigned_to_nat(32u);
v___x_510_ = lean_mk_empty_array_with_capacity(v___x_509_);
v___x_511_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2);
v___x_512_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
lean_ctor_set(v___x_512_, 2, v___x_508_);
lean_ctor_set(v___x_512_, 3, v___x_508_);
lean_ctor_set_usize(v___x_512_, 4, v___x_507_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_box(1);
v___x_514_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3);
v___x_515_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1);
v___x_516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(lean_object* v_lctx_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_auxDeclToFullName_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_auxDeclToFullName_523_ = lean_ctor_get(v_lctx_517_, 2);
lean_inc(v_auxDeclToFullName_523_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_obj_once(&l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4, &l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once, _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4);
v___x_526_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_523_, v_lctx_517_, v___x_525_, v___x_524_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v_auxDeclToFullName_523_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___boxed(lean_object* v_lctx_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_ks_538_; lean_object* v_vs_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_563_; 
v_ks_538_ = lean_ctor_get(v_x_534_, 0);
v_vs_539_ = lean_ctor_get(v_x_534_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_563_ == 0)
{
v___x_541_ = v_x_534_;
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_vs_539_);
lean_inc(v_ks_538_);
lean_dec(v_x_534_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_array_get_size(v_ks_538_);
v___x_544_ = lean_nat_dec_lt(v_x_535_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
lean_dec(v_x_535_);
v___x_545_ = lean_array_push(v_ks_538_, v_x_536_);
v___x_546_ = lean_array_push(v_vs_539_, v_x_537_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_546_);
lean_ctor_set(v___x_541_, 0, v___x_545_);
v___x_548_ = v___x_541_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_object* v_k_x27_550_; uint8_t v___x_551_; 
v_k_x27_550_ = lean_array_fget_borrowed(v_ks_538_, v_x_535_);
v___x_551_ = l_Lean_instBEqMVarId_beq(v_x_536_, v_k_x27_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_553_; 
if (v_isShared_542_ == 0)
{
v___x_553_ = v___x_541_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_ks_538_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_vs_539_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_x_535_, v___x_554_);
lean_dec(v_x_535_);
v_x_534_ = v___x_553_;
v_x_535_ = v___x_555_;
goto _start;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = lean_array_fset(v_ks_538_, v_x_535_, v_x_536_);
v___x_559_ = lean_array_fset(v_vs_539_, v_x_535_, v_x_537_);
lean_dec(v_x_535_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_559_);
lean_ctor_set(v___x_541_, 0, v___x_558_);
v___x_561_ = v___x_541_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(lean_object* v_n_564_, lean_object* v_k_565_, lean_object* v_v_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_n_564_, v___x_567_, v_k_565_, v_v_566_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(lean_object* v_x_570_, size_t v_x_571_, size_t v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v_es_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v_j_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_es_575_ = lean_ctor_get(v_x_570_, 0);
v___x_576_ = ((size_t)31ULL);
v___x_577_ = lean_usize_land(v_x_571_, v___x_576_);
v_j_578_ = lean_usize_to_nat(v___x_577_);
v___x_579_ = lean_array_get_size(v_es_575_);
v___x_580_ = lean_nat_dec_lt(v_j_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_j_578_);
lean_dec(v_x_574_);
lean_dec(v_x_573_);
return v_x_570_;
}
else
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_619_; 
lean_inc_ref(v_es_575_);
v_isSharedCheck_619_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_x_570_, 0);
lean_dec(v_unused_620_);
v___x_582_ = v_x_570_;
v_isShared_583_ = v_isSharedCheck_619_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_x_570_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_619_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_v_584_; lean_object* v___x_585_; lean_object* v_xs_x27_586_; lean_object* v___y_588_; 
v_v_584_ = lean_array_fget(v_es_575_, v_j_578_);
v___x_585_ = lean_box(0);
v_xs_x27_586_ = lean_array_fset(v_es_575_, v_j_578_, v___x_585_);
switch(lean_obj_tag(v_v_584_))
{
case 0:
{
lean_object* v_key_593_; lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_604_; 
v_key_593_ = lean_ctor_get(v_v_584_, 0);
v_val_594_ = lean_ctor_get(v_v_584_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_v_584_);
if (v_isSharedCheck_604_ == 0)
{
v___x_596_ = v_v_584_;
v_isShared_597_ = v_isSharedCheck_604_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_inc(v_key_593_);
lean_dec(v_v_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_604_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
uint8_t v___x_598_; 
v___x_598_ = l_Lean_instBEqMVarId_beq(v_x_573_, v_key_593_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_del_object(v___x_596_);
v___x_599_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_593_, v_val_594_, v_x_573_, v_x_574_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___y_588_ = v___x_600_;
goto v___jp_587_;
}
else
{
lean_object* v___x_602_; 
lean_dec(v_val_594_);
lean_dec(v_key_593_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_x_574_);
lean_ctor_set(v___x_596_, 0, v_x_573_);
v___x_602_ = v___x_596_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_x_573_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_x_574_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
v___y_588_ = v___x_602_;
goto v___jp_587_;
}
}
}
}
case 1:
{
lean_object* v_node_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_617_; 
v_node_605_ = lean_ctor_get(v_v_584_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_v_584_);
if (v_isSharedCheck_617_ == 0)
{
v___x_607_ = v_v_584_;
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_node_605_);
lean_dec(v_v_584_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_609_ = ((size_t)5ULL);
v___x_610_ = lean_usize_shift_right(v_x_571_, v___x_609_);
v___x_611_ = ((size_t)1ULL);
v___x_612_ = lean_usize_add(v_x_572_, v___x_611_);
v___x_613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_node_605_, v___x_610_, v___x_612_, v_x_573_, v_x_574_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_613_);
v___x_615_ = v___x_607_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v___y_588_ = v___x_615_;
goto v___jp_587_;
}
}
}
default: 
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_x_573_);
lean_ctor_set(v___x_618_, 1, v_x_574_);
v___y_588_ = v___x_618_;
goto v___jp_587_;
}
}
v___jp_587_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_array_fset(v_xs_x27_586_, v_j_578_, v___y_588_);
lean_dec(v_j_578_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_589_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v_ks_621_; lean_object* v_vs_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_640_; 
v_ks_621_ = lean_ctor_get(v_x_570_, 0);
v_vs_622_ = lean_ctor_get(v_x_570_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_640_ == 0)
{
v___x_624_ = v_x_570_;
v_isShared_625_ = v_isSharedCheck_640_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_vs_622_);
lean_inc(v_ks_621_);
lean_dec(v_x_570_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_640_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_ks_621_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_vs_622_);
v___x_627_ = v_reuseFailAlloc_639_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v_newNode_628_; size_t v___x_629_; uint8_t v___x_630_; 
v_newNode_628_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v___x_627_, v_x_573_, v_x_574_);
v___x_629_ = ((size_t)7ULL);
v___x_630_ = lean_usize_dec_le(v___x_629_, v_x_572_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_628_);
v___x_632_ = lean_unsigned_to_nat(4u);
v___x_633_ = lean_nat_dec_lt(v___x_631_, v___x_632_);
lean_dec(v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v_ks_634_; lean_object* v_vs_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_ks_634_ = lean_ctor_get(v_newNode_628_, 0);
lean_inc_ref(v_ks_634_);
v_vs_635_ = lean_ctor_get(v_newNode_628_, 1);
lean_inc_ref(v_vs_635_);
lean_dec_ref(v_newNode_628_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0);
v___x_638_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_x_572_, v_ks_634_, v_vs_635_, v___x_636_, v___x_637_);
lean_dec_ref(v_vs_635_);
lean_dec_ref(v_ks_634_);
return v___x_638_;
}
else
{
return v_newNode_628_;
}
}
else
{
return v_newNode_628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(size_t v_depth_641_, lean_object* v_keys_642_, lean_object* v_vals_643_, lean_object* v_i_644_, lean_object* v_entries_645_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_array_get_size(v_keys_642_);
v___x_647_ = lean_nat_dec_lt(v_i_644_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v_i_644_);
return v_entries_645_;
}
else
{
lean_object* v_k_648_; lean_object* v_v_649_; uint64_t v___x_650_; size_t v_h_651_; size_t v___x_652_; lean_object* v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v_h_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_k_648_ = lean_array_fget_borrowed(v_keys_642_, v_i_644_);
v_v_649_ = lean_array_fget_borrowed(v_vals_643_, v_i_644_);
v___x_650_ = l_Lean_instHashableMVarId_hash(v_k_648_);
v_h_651_ = lean_uint64_to_usize(v___x_650_);
v___x_652_ = ((size_t)5ULL);
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_sub(v_depth_641_, v___x_654_);
v___x_656_ = lean_usize_mul(v___x_652_, v___x_655_);
v_h_657_ = lean_usize_shift_right(v_h_651_, v___x_656_);
v___x_658_ = lean_nat_add(v_i_644_, v___x_653_);
lean_dec(v_i_644_);
lean_inc(v_v_649_);
lean_inc(v_k_648_);
v___x_659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_entries_645_, v_h_657_, v_depth_641_, v_k_648_, v_v_649_);
v_i_644_ = v___x_658_;
v_entries_645_ = v___x_659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg___boxed(lean_object* v_depth_661_, lean_object* v_keys_662_, lean_object* v_vals_663_, lean_object* v_i_664_, lean_object* v_entries_665_){
_start:
{
size_t v_depth_boxed_666_; lean_object* v_res_667_; 
v_depth_boxed_666_ = lean_unbox_usize(v_depth_661_);
lean_dec(v_depth_661_);
v_res_667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_boxed_666_, v_keys_662_, v_vals_663_, v_i_664_, v_entries_665_);
lean_dec_ref(v_vals_663_);
lean_dec_ref(v_keys_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
size_t v_x_4386__boxed_673_; size_t v_x_4387__boxed_674_; lean_object* v_res_675_; 
v_x_4386__boxed_673_ = lean_unbox_usize(v_x_669_);
lean_dec(v_x_669_);
v_x_4387__boxed_674_ = lean_unbox_usize(v_x_670_);
lean_dec(v_x_670_);
v_res_675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_668_, v_x_4386__boxed_673_, v_x_4387__boxed_674_, v_x_671_, v_x_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
uint64_t v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_679_ = l_Lean_instHashableMVarId_hash(v_x_677_);
v___x_680_ = lean_uint64_to_usize(v___x_679_);
v___x_681_ = ((size_t)1ULL);
v___x_682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_676_, v___x_680_, v___x_681_, v_x_677_, v_x_678_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(lean_object* v_mvarId_683_, lean_object* v_val_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v_mctx_688_; lean_object* v_cache_689_; lean_object* v_zetaDeltaFVarIds_690_; lean_object* v_postponed_691_; lean_object* v_diag_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_721_; 
v___x_687_ = lean_st_ref_take(v___y_685_);
v_mctx_688_ = lean_ctor_get(v___x_687_, 0);
v_cache_689_ = lean_ctor_get(v___x_687_, 1);
v_zetaDeltaFVarIds_690_ = lean_ctor_get(v___x_687_, 2);
v_postponed_691_ = lean_ctor_get(v___x_687_, 3);
v_diag_692_ = lean_ctor_get(v___x_687_, 4);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_721_ == 0)
{
v___x_694_ = v___x_687_;
v_isShared_695_ = v_isSharedCheck_721_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_diag_692_);
lean_inc(v_postponed_691_);
lean_inc(v_zetaDeltaFVarIds_690_);
lean_inc(v_cache_689_);
lean_inc(v_mctx_688_);
lean_dec(v___x_687_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_721_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_depth_696_; lean_object* v_levelAssignDepth_697_; lean_object* v_lmvarCounter_698_; lean_object* v_mvarCounter_699_; lean_object* v_lDecls_700_; lean_object* v_decls_701_; lean_object* v_userNames_702_; lean_object* v_lAssignment_703_; lean_object* v_eAssignment_704_; lean_object* v_dAssignment_705_; lean_object* v_synthNormMemo_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_720_; 
v_depth_696_ = lean_ctor_get(v_mctx_688_, 0);
v_levelAssignDepth_697_ = lean_ctor_get(v_mctx_688_, 1);
v_lmvarCounter_698_ = lean_ctor_get(v_mctx_688_, 2);
v_mvarCounter_699_ = lean_ctor_get(v_mctx_688_, 3);
v_lDecls_700_ = lean_ctor_get(v_mctx_688_, 4);
v_decls_701_ = lean_ctor_get(v_mctx_688_, 5);
v_userNames_702_ = lean_ctor_get(v_mctx_688_, 6);
v_lAssignment_703_ = lean_ctor_get(v_mctx_688_, 7);
v_eAssignment_704_ = lean_ctor_get(v_mctx_688_, 8);
v_dAssignment_705_ = lean_ctor_get(v_mctx_688_, 9);
v_synthNormMemo_706_ = lean_ctor_get(v_mctx_688_, 10);
v_isSharedCheck_720_ = !lean_is_exclusive(v_mctx_688_);
if (v_isSharedCheck_720_ == 0)
{
v___x_708_ = v_mctx_688_;
v_isShared_709_ = v_isSharedCheck_720_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_synthNormMemo_706_);
lean_inc(v_dAssignment_705_);
lean_inc(v_eAssignment_704_);
lean_inc(v_lAssignment_703_);
lean_inc(v_userNames_702_);
lean_inc(v_decls_701_);
lean_inc(v_lDecls_700_);
lean_inc(v_mvarCounter_699_);
lean_inc(v_lmvarCounter_698_);
lean_inc(v_levelAssignDepth_697_);
lean_inc(v_depth_696_);
lean_dec(v_mctx_688_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_720_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = lean_box(0);
v___x_711_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_704_, v_mvarId_683_, v_val_684_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 8, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_depth_696_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_levelAssignDepth_697_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_lmvarCounter_698_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_mvarCounter_699_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_lDecls_700_);
lean_ctor_set(v_reuseFailAlloc_719_, 5, v_decls_701_);
lean_ctor_set(v_reuseFailAlloc_719_, 6, v_userNames_702_);
lean_ctor_set(v_reuseFailAlloc_719_, 7, v_lAssignment_703_);
lean_ctor_set(v_reuseFailAlloc_719_, 8, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_719_, 9, v_dAssignment_705_);
lean_ctor_set(v_reuseFailAlloc_719_, 10, v_synthNormMemo_706_);
v___x_713_ = v_reuseFailAlloc_719_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_713_);
v___x_715_ = v___x_694_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_cache_689_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_zetaDeltaFVarIds_690_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_postponed_691_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_diag_692_);
v___x_715_ = v_reuseFailAlloc_718_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_st_ref_put(v___y_685_, v___x_715_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_710_);
return v___x_717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(lean_object* v_mvarId_722_, lean_object* v_val_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_722_, v_val_723_, v___y_724_);
lean_dec(v___y_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars(lean_object* v_mvarId_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_727_);
v___x_734_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_727_, v___x_733_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; 
lean_dec_ref_known(v___x_734_, 1);
lean_inc(v_mvarId_727_);
v___x_735_ = l_Lean_MVarId_getDecl(v_mvarId_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v_userName_737_; lean_object* v_lctx_738_; lean_object* v_type_739_; lean_object* v_localInstances_740_; lean_object* v___x_741_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v_userName_737_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_userName_737_);
v_lctx_738_ = lean_ctor_get(v_a_736_, 1);
lean_inc_ref(v_lctx_738_);
v_type_739_ = lean_ctor_get(v_a_736_, 2);
lean_inc_ref(v_type_739_);
v_localInstances_740_ = lean_ctor_get(v_a_736_, 4);
lean_inc_ref(v_localInstances_740_);
lean_dec(v_a_736_);
v___x_741_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_738_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v_a_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_739_, v_a_729_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref(v___x_743_);
v___x_745_ = 2;
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_742_, v_localInstances_740_, v_a_744_, v___x_745_, v_userName_737_, v___x_746_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_757_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc_n(v_a_748_, 2);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_727_, v_a_748_, v_a_729_);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_758_);
v___x_751_ = v___x_749_;
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
else
{
lean_dec(v___x_749_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = l_Lean_Expr_mvarId_x21(v_a_748_);
lean_dec(v_a_748_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_mvarId_727_);
v_a_759_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_747_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_747_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_localInstances_740_);
lean_dec_ref(v_type_739_);
lean_dec(v_userName_737_);
lean_dec(v_mvarId_727_);
v_a_767_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_741_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_741_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_mvarId_727_);
v_a_775_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_735_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_735_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_mvarId_727_);
v_a_783_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_734_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_734_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars___boxed(lean_object* v_mvarId_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_MVarId_instantiateGoalMVars(v_mvarId_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(lean_object* v_mvarId_798_, lean_object* v_val_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_798_, v_val_799_, v___y_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(lean_object* v_mvarId_806_, lean_object* v_val_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(v_mvarId_806_, v_val_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(lean_object* v_00_u03b4_814_, lean_object* v_t_815_, lean_object* v_k_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_815_, v_k_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b4_818_, lean_object* v_t_819_, lean_object* v_k_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(v_00_u03b4_818_, v_t_819_, v_k_820_);
lean_dec(v_k_820_);
lean_dec(v_t_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(lean_object* v_00_u03b2_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_x_823_, v_x_824_, v_x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_827_, lean_object* v_x_828_, size_t v_x_829_, size_t v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_828_, v_x_829_, v_x_830_, v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_4742__boxed_840_; size_t v_x_4743__boxed_841_; lean_object* v_res_842_; 
v_x_4742__boxed_840_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_x_4743__boxed_841_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_834_, v_x_835_, v_x_4742__boxed_840_, v_x_4743__boxed_841_, v_x_838_, v_x_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_843_, lean_object* v_n_844_, lean_object* v_k_845_, lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v_n_844_, v_k_845_, v_v_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_848_, size_t v_depth_849_, lean_object* v_keys_850_, lean_object* v_vals_851_, lean_object* v_heq_852_, lean_object* v_i_853_, lean_object* v_entries_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_849_, v_keys_850_, v_vals_851_, v_i_853_, v_entries_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(lean_object* v_00_u03b2_856_, lean_object* v_depth_857_, lean_object* v_keys_858_, lean_object* v_vals_859_, lean_object* v_heq_860_, lean_object* v_i_861_, lean_object* v_entries_862_){
_start:
{
size_t v_depth_boxed_863_; lean_object* v_res_864_; 
v_depth_boxed_863_ = lean_unbox_usize(v_depth_857_);
lean_dec(v_depth_857_);
v_res_864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(v_00_u03b2_856_, v_depth_boxed_863_, v_keys_858_, v_vals_859_, v_heq_860_, v_i_861_, v_entries_862_);
lean_dec_ref(v_vals_859_);
lean_dec_ref(v_keys_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_x_866_, v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(lean_object* v_k_871_, lean_object* v_b_872_, lean_object* v_c_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_874_);
v___x_879_ = lean_apply_7(v_k_871_, v_b_872_, v_c_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, lean_box(0));
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(lean_object* v_k_880_, lean_object* v_b_881_, lean_object* v_c_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(v_k_880_, v_b_881_, v_c_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(lean_object* v_e_889_, lean_object* v_k_890_, uint8_t v_cleanupAnnotations_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___f_897_; uint8_t v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___f_897_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_897_, 0, v_k_890_);
v___x_898_ = 1;
v___x_899_ = 0;
v___x_900_ = lean_box(0);
v___x_901_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_889_, v___x_898_, v___x_899_, v___x_898_, v___x_899_, v___x_900_, v___f_897_, v_cleanupAnnotations_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_910_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_901_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_901_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_918_, lean_object* v_k_919_, lean_object* v_cleanupAnnotations_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_926_; lean_object* v_res_927_; 
v_cleanupAnnotations_boxed_926_ = lean_unbox(v_cleanupAnnotations_920_);
v_res_927_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_918_, v_k_919_, v_cleanupAnnotations_boxed_926_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(lean_object* v_00_u03b1_928_, lean_object* v_e_929_, lean_object* v_k_930_, uint8_t v_cleanupAnnotations_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_929_, v_k_930_, v_cleanupAnnotations_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___boxed(lean_object* v_00_u03b1_938_, lean_object* v_e_939_, lean_object* v_k_940_, lean_object* v_cleanupAnnotations_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_947_; lean_object* v_res_948_; 
v_cleanupAnnotations_boxed_947_ = lean_unbox(v_cleanupAnnotations_941_);
v_res_948_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(v_00_u03b1_938_, v_e_939_, v_k_940_, v_cleanupAnnotations_boxed_947_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(lean_object* v_mvarId_949_, lean_object* v_x_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_949_, v_x_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_956_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_956_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg___boxed(lean_object* v_mvarId_973_, lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_973_, v_x_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(lean_object* v_00_u03b1_981_, lean_object* v_mvarId_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___boxed(lean_object* v_00_u03b1_990_, lean_object* v_mvarId_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(v_00_u03b1_990_, v_mvarId_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t v___x_999_, uint8_t v___x_1000_, lean_object* v_xs_1001_, lean_object* v_body_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = 1;
v___x_1009_ = l_Lean_Meta_mkForallFVars(v_xs_1001_, v_body_1002_, v___x_999_, v___x_1000_, v___x_1000_, v___x_1008_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_xs_1012_, lean_object* v_body_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v___x_1776__boxed_1019_; uint8_t v___x_1777__boxed_1020_; lean_object* v_res_1021_; 
v___x_1776__boxed_1019_ = lean_unbox(v___x_1010_);
v___x_1777__boxed_1020_ = lean_unbox(v___x_1011_);
v_res_1021_ = l_Lean_MVarId_abstractMVars___lam__0(v___x_1776__boxed_1019_, v___x_1777__boxed_1020_, v_xs_1012_, v_body_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec_ref(v_xs_1012_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object* v_a_1022_, uint8_t v___x_1023_, lean_object* v___f_1024_, lean_object* v_mvarId_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Meta_abstractMVars(v_a_1022_, v___x_1023_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v_mvars_1033_; lean_object* v_expr_1034_; lean_object* v___x_1035_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_mvars_1033_ = lean_ctor_get(v_a_1032_, 1);
lean_inc_ref(v_mvars_1033_);
v_expr_1034_ = lean_ctor_get(v_a_1032_, 2);
lean_inc_ref(v_expr_1034_);
lean_dec(v_a_1032_);
v___x_1035_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_expr_1034_, v___f_1024_, v___x_1023_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
lean_inc(v_mvarId_1025_);
v___x_1037_ = l_Lean_MVarId_getTag(v_mvarId_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1036_, v_a_1038_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1050_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc_n(v_a_1040_, 2);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l_Lean_mkAppN(v_a_1040_, v_mvars_1033_);
lean_dec_ref(v_mvars_1033_);
v___x_1042_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1025_, v___x_1041_, v___y_1027_);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1042_, 0);
lean_dec(v_unused_1051_);
v___x_1044_ = v___x_1042_;
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
else
{
lean_dec(v___x_1042_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = l_Lean_Expr_mvarId_x21(v_a_1040_);
lean_dec(v_a_1040_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_mvars_1033_);
lean_dec(v_mvarId_1025_);
v_a_1052_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1039_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1039_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_a_1036_);
lean_dec_ref(v_mvars_1033_);
lean_dec(v_mvarId_1025_);
v_a_1060_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1037_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1037_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_mvars_1033_);
lean_dec(v_mvarId_1025_);
v_a_1068_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1035_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1035_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_mvarId_1025_);
lean_dec_ref(v___f_1024_);
v_a_1076_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1031_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1031_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object* v_a_1084_, lean_object* v___x_1085_, lean_object* v___f_1086_, lean_object* v_mvarId_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v___x_1802__boxed_1093_; lean_object* v_res_1094_; 
v___x_1802__boxed_1093_ = lean_unbox(v___x_1085_);
v_res_1094_ = l_Lean_MVarId_abstractMVars___lam__1(v_a_1084_, v___x_1802__boxed_1093_, v___f_1086_, v_mvarId_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars(lean_object* v_mvarId_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1095_);
v___x_1102_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1095_, v___x_1101_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1102_, 1);
lean_inc(v_mvarId_1095_);
v___x_1103_ = l_Lean_MVarId_getType(v_mvarId_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1121_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_1104_, v_a_1097_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1121_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1121_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Lean_Expr_hasExprMVar(v_a_1106_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_a_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v_mvarId_1095_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_mvarId_1095_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; 
lean_del_object(v___x_1108_);
v___x_1114_ = 0;
v___x_1115_ = lean_box(v___x_1114_);
v___x_1116_ = lean_box(v___x_1110_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1117_, 0, v___x_1115_);
lean_closure_set(v___f_1117_, 1, v___x_1116_);
v___x_1118_ = lean_box(v___x_1114_);
lean_inc(v_mvarId_1095_);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1119_, 0, v_a_1106_);
lean_closure_set(v___f_1119_, 1, v___x_1118_);
lean_closure_set(v___f_1119_, 2, v___f_1117_);
lean_closure_set(v___f_1119_, 3, v_mvarId_1095_);
v___x_1120_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1095_, v___f_1119_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_mvarId_1095_);
v_a_1122_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1103_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1103_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_mvarId_1095_);
v_a_1130_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1102_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1102_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___boxed(lean_object* v_mvarId_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_MVarId_abstractMVars(v_mvarId_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object* v_mvarId_1145_, lean_object* v___x_1146_, lean_object* v_f_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
lean_inc(v_mvarId_1145_);
v___x_1153_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1145_, v___x_1146_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1154_; 
lean_dec_ref_known(v___x_1153_, 1);
lean_inc(v_mvarId_1145_);
v___x_1154_ = l_Lean_MVarId_getTag(v_mvarId_1145_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
lean_inc(v_mvarId_1145_);
v___x_1156_ = l_Lean_MVarId_getType(v_mvarId_1145_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1150_);
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
v___x_1158_ = lean_apply_6(v_f_1147_, v_a_1157_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1159_, v_a_1155_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v___y_1148_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc_n(v_a_1161_, 2);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1162_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1145_, v_a_1161_, v___y_1149_);
lean_dec(v___y_1149_);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1171_);
v___x_1164_ = v___x_1162_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v___x_1162_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = l_Lean_Expr_mvarId_x21(v_a_1161_);
lean_dec(v_a_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v___y_1149_);
lean_dec(v_mvarId_1145_);
v_a_1172_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1160_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1160_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1155_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v_mvarId_1145_);
v_a_1180_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1158_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1158_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_a_1155_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v_f_1147_);
lean_dec(v_mvarId_1145_);
v_a_1188_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1156_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1156_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v_f_1147_);
lean_dec(v_mvarId_1145_);
v_a_1196_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1154_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1154_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v_f_1147_);
lean_dec(v_mvarId_1145_);
v_a_1204_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1153_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1153_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0___boxed(lean_object* v_mvarId_1212_, lean_object* v___x_1213_, lean_object* v_f_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_MVarId_transformTarget___lam__0(v_mvarId_1212_, v___x_1213_, v_f_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object* v_mvarId_1221_, lean_object* v_f_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___x_1228_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1221_);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_MVarId_transformTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1229_, 0, v_mvarId_1221_);
lean_closure_set(v___f_1229_, 1, v___x_1228_);
lean_closure_set(v___f_1229_, 2, v_f_1222_);
v___x_1230_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1221_, v___f_1229_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___boxed(lean_object* v_mvarId_1231_, lean_object* v_f_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_MVarId_transformTarget(v_mvarId_1231_, v_f_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object* v_mvarId_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_MVarId_unfoldReducible___closed__0));
v___x_1247_ = l_Lean_MVarId_transformTarget(v_mvarId_1240_, v___x_1246_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible___boxed(lean_object* v_mvarId_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_MVarId_unfoldReducible(v_mvarId_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object* v_x_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Core_betaReduce(v_x_1255_, v___y_1258_, v___y_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_MVarId_betaReduce___lam__0(v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object* v_mvarId_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___f_1276_; lean_object* v___x_1277_; 
v___f_1276_ = ((lean_object*)(l_Lean_MVarId_betaReduce___closed__0));
v___x_1277_ = l_Lean_MVarId_transformTarget(v_mvarId_1270_, v___f_1276_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___boxed(lean_object* v_mvarId_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_MVarId_betaReduce(v_mvarId_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
return v_res_1284_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__1));
v___x_1290_ = l_Lean_mkConst(v___x_1289_, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__5));
v___x_1298_ = l_Lean_mkConst(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object* v_mvarId_1299_, lean_object* v___x_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
lean_inc(v_mvarId_1299_);
v___x_1306_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1299_, v___x_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v___x_1307_; 
lean_dec_ref_known(v___x_1306_, 1);
lean_inc(v_mvarId_1299_);
v___x_1307_ = l_Lean_MVarId_getType(v_mvarId_1299_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1362_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1362_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1362_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint8_t v___x_1312_; 
lean_inc(v_a_1308_);
v___x_1312_ = l_Lean_Expr_isFalse(v_a_1308_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_del_object(v___x_1310_);
lean_inc(v_a_1308_);
v___x_1313_ = l_Lean_mkNot(v_a_1308_);
v___x_1314_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__2, &l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2);
v___x_1315_ = l_Lean_mkArrow(v___x_1313_, v___x_1314_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
lean_inc(v_mvarId_1299_);
v___x_1317_ = l_Lean_MVarId_getTag(v_mvarId_1299_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1316_, v_a_1318_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1332_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc_n(v_a_1320_, 2);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__6, &l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6);
v___x_1322_ = l_Lean_mkAppB(v___x_1321_, v_a_1308_, v_a_1320_);
v___x_1323_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1299_, v___x_1322_, v___y_1302_);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1323_, 0);
lean_dec(v_unused_1333_);
v___x_1325_ = v___x_1323_;
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v___x_1323_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1327_ = l_Lean_Expr_mvarId_x21(v_a_1320_);
lean_dec(v_a_1320_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1328_);
v___x_1330_ = v___x_1325_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_a_1308_);
lean_dec(v_mvarId_1299_);
v_a_1334_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1319_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1319_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_a_1316_);
lean_dec(v_a_1308_);
lean_dec(v_mvarId_1299_);
v_a_1342_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1317_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1317_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_a_1308_);
lean_dec(v_mvarId_1299_);
v_a_1350_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1315_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1315_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_dec(v_a_1308_);
lean_dec(v_mvarId_1299_);
v___x_1358_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1358_);
v___x_1360_ = v___x_1310_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_mvarId_1299_);
v_a_1363_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1307_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1307_);
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
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_mvarId_1299_);
v_a_1371_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1306_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1306_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object* v_mvarId_1379_, lean_object* v___x_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_MVarId_byContra_x3f___lam__0(v_mvarId_1379_, v___x_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object* v_mvarId_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___x_1399_; 
v___x_1397_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___closed__1));
lean_inc(v_mvarId_1391_);
v___f_1398_ = lean_alloc_closure((void*)(l_Lean_MVarId_byContra_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1398_, 0, v_mvarId_1391_);
lean_closure_set(v___f_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1391_, v___f_1398_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___boxed(lean_object* v_mvarId_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1406_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0));
v___x_1409_ = l_Lean_stringToMessageData(v___x_1408_);
return v___x_1409_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2));
v___x_1412_ = l_Lean_stringToMessageData(v___x_1411_);
return v___x_1412_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4));
v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(lean_object* v_as_x27_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
if (lean_obj_tag(v_as_x27_1416_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_b_1417_);
return v___x_1423_;
}
else
{
lean_object* v_head_1424_; lean_object* v_tail_1425_; lean_object* v___x_1426_; 
v_head_1424_ = lean_ctor_get(v_as_x27_1416_, 0);
v_tail_1425_ = lean_ctor_get(v_as_x27_1416_, 1);
lean_inc(v_head_1424_);
lean_inc(v_b_1417_);
v___x_1426_ = l_Lean_MVarId_clear(v_b_1417_, v_head_1424_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; 
lean_dec(v_b_1417_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v_as_x27_1416_ = v_tail_1425_;
v_b_1417_ = v_a_1427_;
goto _start;
}
else
{
lean_object* v_a_1429_; uint8_t v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1426_, 0);
v___x_1430_ = l_Lean_Exception_isInterrupt(v_a_1429_);
if (v___x_1430_ == 0)
{
uint8_t v___x_1431_; 
lean_inc(v_a_1429_);
v___x_1431_ = l_Lean_Exception_isRuntime(v_a_1429_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1426_, 0);
lean_dec(v_unused_1471_);
v___x_1433_ = v___x_1426_;
v_isShared_1434_ = v_isSharedCheck_1470_;
goto v_resetjp_1432_;
}
else
{
lean_dec(v___x_1426_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1470_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; 
lean_inc(v_head_1424_);
v___x_1435_ = l_Lean_FVarId_getDecl___redArg(v_head_1424_, v___y_1418_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; uint8_t v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Lean_LocalDecl_isAuxDecl(v_a_1436_);
if (v___x_1437_ == 0)
{
lean_dec(v_a_1436_);
lean_del_object(v___x_1433_);
v_as_x27_1416_ = v_tail_1425_;
goto _start;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1439_ = l_Lean_LocalDecl_userName(v_a_1436_);
lean_dec(v_a_1436_);
v___x_1440_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_1441_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
v___x_1442_ = l_Lean_MessageData_ofName(v___x_1439_);
lean_inc_ref(v___x_1442_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___x_1442_);
v___x_1447_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
v___x_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1448_);
v___x_1450_ = v___x_1433_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; 
lean_inc(v_b_1417_);
v___x_1451_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1440_, v_b_1417_, v___x_1450_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_dec_ref_known(v___x_1451_, 1);
v_as_x27_1416_ = v_tail_1425_;
goto _start;
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_b_1417_);
v_a_1453_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1451_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1451_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_del_object(v___x_1433_);
lean_dec(v_b_1417_);
v_a_1462_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1435_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1435_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
else
{
lean_dec(v_b_1417_);
return v___x_1426_;
}
}
else
{
lean_dec(v_b_1417_);
return v___x_1426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(lean_object* v_as_x27_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1472_, v_b_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v_as_x27_1472_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_1480_, size_t v_sz_1481_, size_t v_i_1482_, lean_object* v_b_1483_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_usize_dec_lt(v_i_1482_, v_sz_1481_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1483_);
return v___x_1486_;
}
else
{
lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1505_; 
v_snd_1487_ = lean_ctor_get(v_b_1483_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_b_1483_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_b_1483_, 0);
lean_dec(v_unused_1506_);
v___x_1489_ = v_b_1483_;
v_isShared_1490_ = v_isSharedCheck_1505_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_dec(v_b_1483_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1505_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v_a_1493_; lean_object* v_a_1500_; 
v___x_1491_ = lean_box(0);
v_a_1500_ = lean_array_uget_borrowed(v_as_1480_, v_i_1482_);
if (lean_obj_tag(v_a_1500_) == 0)
{
v_a_1493_ = v_snd_1487_;
goto v___jp_1492_;
}
else
{
lean_object* v_val_1501_; uint8_t v___x_1502_; 
v_val_1501_ = lean_ctor_get(v_a_1500_, 0);
v___x_1502_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1501_);
if (v___x_1502_ == 0)
{
v_a_1493_ = v_snd_1487_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = l_Lean_LocalDecl_fvarId(v_val_1501_);
v___x_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v_snd_1487_);
v_a_1493_ = v___x_1504_;
goto v___jp_1492_;
}
}
v___jp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v_a_1493_);
lean_ctor_set(v___x_1489_, 0, v___x_1491_);
v___x_1495_ = v___x_1489_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1493_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
size_t v___x_1496_; size_t v___x_1497_; 
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1482_, v___x_1496_);
v_i_1482_ = v___x_1497_;
v_b_1483_ = v___x_1495_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_1507_, lean_object* v_sz_1508_, lean_object* v_i_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_){
_start:
{
size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1508_);
lean_dec(v_sz_1508_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1507_, v_sz_boxed_1512_, v_i_boxed_1513_, v_b_1510_);
lean_dec_ref(v_as_1507_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(lean_object* v_as_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_lt(v_i_1517_, v_sz_1516_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1518_);
return v___x_1525_;
}
else
{
lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1544_; 
v_snd_1526_ = lean_ctor_get(v_b_1518_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_b_1518_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v_b_1518_, 0);
lean_dec(v_unused_1545_);
v___x_1528_ = v_b_1518_;
v_isShared_1529_ = v_isSharedCheck_1544_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_dec(v_b_1518_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1544_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v_a_1532_; lean_object* v_a_1539_; 
v___x_1530_ = lean_box(0);
v_a_1539_ = lean_array_uget_borrowed(v_as_1515_, v_i_1517_);
if (lean_obj_tag(v_a_1539_) == 0)
{
v_a_1532_ = v_snd_1526_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1540_; uint8_t v___x_1541_; 
v_val_1540_ = lean_ctor_get(v_a_1539_, 0);
v___x_1541_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1540_);
if (v___x_1541_ == 0)
{
v_a_1532_ = v_snd_1526_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_LocalDecl_fvarId(v_val_1540_);
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v_snd_1526_);
v_a_1532_ = v___x_1543_;
goto v___jp_1531_;
}
}
v___jp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_a_1532_);
lean_ctor_set(v___x_1528_, 0, v___x_1530_);
v___x_1534_ = v___x_1528_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_a_1532_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_add(v_i_1517_, v___x_1535_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1515_, v_sz_1516_, v___x_1536_, v___x_1534_);
return v___x_1537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1546_, lean_object* v_sz_1547_, lean_object* v_i_1548_, lean_object* v_b_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
size_t v_sz_boxed_1555_; size_t v_i_boxed_1556_; lean_object* v_res_1557_; 
v_sz_boxed_1555_ = lean_unbox_usize(v_sz_1547_);
lean_dec(v_sz_1547_);
v_i_boxed_1556_ = lean_unbox_usize(v_i_1548_);
lean_dec(v_i_1548_);
v_res_1557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_1546_, v_sz_boxed_1555_, v_i_boxed_1556_, v_b_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec_ref(v_as_1546_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object* v_init_1558_, lean_object* v_n_1559_, lean_object* v_b_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
if (lean_obj_tag(v_n_1559_) == 0)
{
lean_object* v_cs_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v_cs_1566_ = lean_ctor_get(v_n_1559_, 0);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v_b_1560_);
v_sz_1569_ = lean_array_size(v_cs_1566_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1558_, v_cs_1566_, v_sz_1569_, v___x_1570_, v___x_1568_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1586_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1586_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1586_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_fst_1576_; 
v_fst_1576_ = lean_ctor_get(v_a_1572_, 0);
if (lean_obj_tag(v_fst_1576_) == 0)
{
lean_object* v_snd_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v_snd_1577_ = lean_ctor_get(v_a_1572_, 1);
lean_inc(v_snd_1577_);
lean_dec(v_a_1572_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_snd_1577_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1578_);
v___x_1580_ = v___x_1574_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
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
lean_object* v_val_1582_; lean_object* v___x_1584_; 
lean_inc_ref(v_fst_1576_);
lean_dec(v_a_1572_);
v_val_1582_ = lean_ctor_get(v_fst_1576_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_fst_1576_, 1);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v_val_1582_);
v___x_1584_ = v___x_1574_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_val_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1571_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1571_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_vs_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
v_vs_1595_ = lean_ctor_get(v_n_1559_, 0);
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v_b_1560_);
v_sz_1598_ = lean_array_size(v_vs_1595_);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_1595_, v_sz_1598_, v___x_1599_, v___x_1597_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1615_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1615_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1615_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_fst_1605_; 
v_fst_1605_ = lean_ctor_get(v_a_1601_, 0);
if (lean_obj_tag(v_fst_1605_) == 0)
{
lean_object* v_snd_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v_snd_1606_ = lean_ctor_get(v_a_1601_, 1);
lean_inc(v_snd_1606_);
lean_dec(v_a_1601_);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_snd_1606_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1607_);
v___x_1609_ = v___x_1603_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
else
{
lean_object* v_val_1611_; lean_object* v___x_1613_; 
lean_inc_ref(v_fst_1605_);
lean_dec(v_a_1601_);
v_val_1611_ = lean_ctor_get(v_fst_1605_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v_fst_1605_, 1);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_val_1611_);
v___x_1613_ = v___x_1603_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_val_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1600_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1600_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object* v_init_1624_, lean_object* v_as_1625_, size_t v_sz_1626_, size_t v_i_1627_, lean_object* v_b_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_usize_dec_lt(v_i_1627_, v_sz_1626_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v_b_1628_);
return v___x_1635_;
}
else
{
lean_object* v_snd_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1670_; 
v_snd_1636_ = lean_ctor_get(v_b_1628_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_b_1628_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_b_1628_, 0);
lean_dec(v_unused_1671_);
v___x_1638_ = v_b_1628_;
v_isShared_1639_ = v_isSharedCheck_1670_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_snd_1636_);
lean_dec(v_b_1628_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1670_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v_a_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
v_a_1641_ = lean_array_uget_borrowed(v_as_1625_, v_i_1627_);
lean_inc(v_snd_1636_);
v___x_1642_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1624_, v_a_1641_, v_snd_1636_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1661_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1661_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1661_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
if (lean_obj_tag(v_a_1643_) == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_a_1643_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1647_);
v___x_1649_ = v___x_1638_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_snd_1636_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
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
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; 
lean_del_object(v___x_1645_);
lean_dec(v_snd_1636_);
v_a_1654_ = lean_ctor_get(v_a_1643_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v_a_1643_, 1);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v_a_1654_);
lean_ctor_set(v___x_1638_, 0, v___x_1640_);
v___x_1656_ = v___x_1638_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1654_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
size_t v___x_1657_; size_t v___x_1658_; 
v___x_1657_ = ((size_t)1ULL);
v___x_1658_ = lean_usize_add(v_i_1627_, v___x_1657_);
v_i_1627_ = v___x_1658_;
v_b_1628_ = v___x_1656_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_del_object(v___x_1638_);
lean_dec(v_snd_1636_);
v_a_1662_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1642_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1642_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1672_, lean_object* v_as_1673_, lean_object* v_sz_1674_, lean_object* v_i_1675_, lean_object* v_b_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
size_t v_sz_boxed_1682_; size_t v_i_boxed_1683_; lean_object* v_res_1684_; 
v_sz_boxed_1682_ = lean_unbox_usize(v_sz_1674_);
lean_dec(v_sz_1674_);
v_i_boxed_1683_ = lean_unbox_usize(v_i_1675_);
lean_dec(v_i_1675_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1672_, v_as_1673_, v_sz_boxed_1682_, v_i_boxed_1683_, v_b_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_as_1673_);
lean_dec(v_init_1672_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object* v_init_1685_, lean_object* v_n_1686_, lean_object* v_b_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1685_, v_n_1686_, v_b_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec_ref(v_n_1686_);
lean_dec(v_init_1685_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1694_, size_t v_sz_1695_, size_t v_i_1696_, lean_object* v_b_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_lt(v_i_1696_, v_sz_1695_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_b_1697_);
return v___x_1700_;
}
else
{
lean_object* v_snd_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1719_; 
v_snd_1701_ = lean_ctor_get(v_b_1697_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_b_1697_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v_b_1697_, 0);
lean_dec(v_unused_1720_);
v___x_1703_ = v_b_1697_;
v_isShared_1704_ = v_isSharedCheck_1719_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snd_1701_);
lean_dec(v_b_1697_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1719_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v_a_1707_; lean_object* v_a_1714_; 
v___x_1705_ = lean_box(0);
v_a_1714_ = lean_array_uget_borrowed(v_as_1694_, v_i_1696_);
if (lean_obj_tag(v_a_1714_) == 0)
{
v_a_1707_ = v_snd_1701_;
goto v___jp_1706_;
}
else
{
lean_object* v_val_1715_; uint8_t v___x_1716_; 
v_val_1715_ = lean_ctor_get(v_a_1714_, 0);
v___x_1716_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1715_);
if (v___x_1716_ == 0)
{
v_a_1707_ = v_snd_1701_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = l_Lean_LocalDecl_fvarId(v_val_1715_);
v___x_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v_snd_1701_);
v_a_1707_ = v___x_1718_;
goto v___jp_1706_;
}
}
v___jp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_a_1707_);
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1709_ = v___x_1703_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_a_1707_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
size_t v___x_1710_; size_t v___x_1711_; 
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1696_, v___x_1710_);
v_i_1696_ = v___x_1711_;
v_b_1697_ = v___x_1709_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1721_, lean_object* v_sz_1722_, lean_object* v_i_1723_, lean_object* v_b_1724_, lean_object* v___y_1725_){
_start:
{
size_t v_sz_boxed_1726_; size_t v_i_boxed_1727_; lean_object* v_res_1728_; 
v_sz_boxed_1726_ = lean_unbox_usize(v_sz_1722_);
lean_dec(v_sz_1722_);
v_i_boxed_1727_ = lean_unbox_usize(v_i_1723_);
lean_dec(v_i_1723_);
v_res_1728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1721_, v_sz_boxed_1726_, v_i_boxed_1727_, v_b_1724_);
lean_dec_ref(v_as_1721_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(lean_object* v_as_1729_, size_t v_sz_1730_, size_t v_i_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_lt(v_i_1731_, v_sz_1730_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1732_);
return v___x_1739_;
}
else
{
lean_object* v_snd_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1758_; 
v_snd_1740_ = lean_ctor_get(v_b_1732_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_b_1732_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v_b_1732_, 0);
lean_dec(v_unused_1759_);
v___x_1742_ = v_b_1732_;
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snd_1740_);
lean_dec(v_b_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v_a_1746_; lean_object* v_a_1753_; 
v___x_1744_ = lean_box(0);
v_a_1753_ = lean_array_uget_borrowed(v_as_1729_, v_i_1731_);
if (lean_obj_tag(v_a_1753_) == 0)
{
v_a_1746_ = v_snd_1740_;
goto v___jp_1745_;
}
else
{
lean_object* v_val_1754_; uint8_t v___x_1755_; 
v_val_1754_ = lean_ctor_get(v_a_1753_, 0);
v___x_1755_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1754_);
if (v___x_1755_ == 0)
{
v_a_1746_ = v_snd_1740_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = l_Lean_LocalDecl_fvarId(v_val_1754_);
v___x_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_snd_1740_);
v_a_1746_ = v___x_1757_;
goto v___jp_1745_;
}
}
v___jp_1745_:
{
lean_object* v___x_1748_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_a_1746_);
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1748_ = v___x_1742_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_a_1746_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1731_, v___x_1749_);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1729_, v_sz_1730_, v___x_1750_, v___x_1748_);
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(lean_object* v_as_1760_, lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
size_t v_sz_boxed_1769_; size_t v_i_boxed_1770_; lean_object* v_res_1771_; 
v_sz_boxed_1769_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1770_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_1760_, v_sz_boxed_1769_, v_i_boxed_1770_, v_b_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v_as_1760_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(lean_object* v_t_1772_, lean_object* v_init_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_root_1779_; lean_object* v_tail_1780_; lean_object* v___x_1781_; 
v_root_1779_ = lean_ctor_get(v_t_1772_, 0);
v_tail_1780_ = lean_ctor_get(v_t_1772_, 1);
lean_inc(v_init_1773_);
v___x_1781_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1773_, v_root_1779_, v_init_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v_init_1773_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1818_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1818_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1818_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
if (lean_obj_tag(v_a_1782_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; 
v_a_1786_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v_a_1782_, 1);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v_a_1786_);
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; size_t v_sz_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1784_);
v_a_1790_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v_a_1782_, 1);
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v_a_1790_);
v_sz_1793_ = lean_array_size(v_tail_1780_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_1780_, v_sz_1793_, v___x_1794_, v___x_1792_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1809_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1809_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1809_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_fst_1800_; 
v_fst_1800_ = lean_ctor_get(v_a_1796_, 0);
if (lean_obj_tag(v_fst_1800_) == 0)
{
lean_object* v_snd_1801_; lean_object* v___x_1803_; 
v_snd_1801_ = lean_ctor_get(v_a_1796_, 1);
lean_inc(v_snd_1801_);
lean_dec(v_a_1796_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_snd_1801_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_snd_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
else
{
lean_object* v_val_1805_; lean_object* v___x_1807_; 
lean_inc_ref(v_fst_1800_);
lean_dec(v_a_1796_);
v_val_1805_ = lean_ctor_get(v_fst_1800_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v_fst_1800_, 1);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_val_1805_);
v___x_1807_ = v___x_1798_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_val_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1795_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1795_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
v_a_1819_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1781_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1781_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(lean_object* v_t_1827_, lean_object* v_init_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_t_1827_, v_init_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_t_1827_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0(lean_object* v_mvarId_1835_, lean_object* v___x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
lean_inc(v_mvarId_1835_);
v___x_1842_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1835_, v___x_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_lctx_1843_; lean_object* v_decls_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1842_, 1);
v_lctx_1843_ = lean_ctor_get(v___y_1837_, 2);
v_decls_1844_ = lean_ctor_get(v_lctx_1843_, 1);
v___x_1845_ = lean_box(0);
v___x_1846_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_decls_1844_, v___x_1845_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1856_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint8_t v___x_1851_; 
v___x_1851_ = l_List_isEmpty___redArg(v_a_1847_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_del_object(v___x_1849_);
v___x_1852_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_a_1847_, v_mvarId_1835_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v_a_1847_);
return v___x_1852_;
}
else
{
lean_object* v___x_1854_; 
lean_dec(v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_mvarId_1835_);
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_mvarId_1835_);
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
lean_dec(v_mvarId_1835_);
v_a_1857_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1846_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1846_);
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
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_mvarId_1835_);
v_a_1865_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1842_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1842_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0___boxed(lean_object* v_mvarId_1873_, lean_object* v___x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_MVarId_clearImplDetails___lam__0(v_mvarId_1873_, v___x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails(lean_object* v_mvarId_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; 
v___x_1891_ = ((lean_object*)(l_Lean_MVarId_clearImplDetails___closed__1));
lean_inc(v_mvarId_1885_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearImplDetails___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1892_, 0, v_mvarId_1885_);
lean_closure_set(v___f_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1885_, v___f_1892_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___boxed(lean_object* v_mvarId_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_MVarId_clearImplDetails(v_mvarId_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(lean_object* v_as_1901_, lean_object* v_as_x27_1902_, lean_object* v_b_1903_, lean_object* v_a_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1902_, v_b_1903_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___boxed(lean_object* v_as_1911_, lean_object* v_as_x27_1912_, lean_object* v_b_1913_, lean_object* v_a_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(v_as_1911_, v_as_x27_1912_, v_b_1913_, v_a_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v_as_x27_1912_);
lean_dec(v_as_1911_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(lean_object* v_as_1921_, size_t v_sz_1922_, size_t v_i_1923_, lean_object* v_b_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1921_, v_sz_1922_, v_i_1923_, v_b_1924_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1931_, lean_object* v_sz_1932_, lean_object* v_i_1933_, lean_object* v_b_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
size_t v_sz_boxed_1940_; size_t v_i_boxed_1941_; lean_object* v_res_1942_; 
v_sz_boxed_1940_ = lean_unbox_usize(v_sz_1932_);
lean_dec(v_sz_1932_);
v_i_boxed_1941_ = lean_unbox_usize(v_i_1933_);
lean_dec(v_i_1933_);
v_res_1942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_1931_, v_sz_boxed_1940_, v_i_boxed_1941_, v_b_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec_ref(v_as_1931_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1943_, size_t v_sz_1944_, size_t v_i_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1943_, v_sz_1944_, v_i_1945_, v_b_1946_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1953_, lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_b_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
size_t v_sz_boxed_1962_; size_t v_i_boxed_1963_; lean_object* v_res_1964_; 
v_sz_boxed_1962_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1963_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_1953_, v_sz_boxed_1962_, v_i_boxed_1963_, v_b_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec_ref(v_as_1953_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object* v_e_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
switch(lean_obj_tag(v_e_1965_))
{
case 8:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_e_1965_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
case 6:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_e_1965_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
case 10:
{
lean_object* v_expr_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_expr_1973_ = lean_ctor_get(v_e_1965_, 1);
lean_inc_ref(v_expr_1973_);
lean_dec_ref_known(v_e_1965_, 2);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_expr_1973_);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
default: 
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_e_1965_);
v___x_1977_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object* v_e_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object* v_e_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_e_1984_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object* v_e_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_object* v_00_u03b1_1995_, lean_object* v_x_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_apply_1(v_x_1996_, lean_box(0));
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2002_, lean_object* v_x_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(v_00_u03b1_2002_, v_x_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_2008_, lean_object* v_x_2009_){
_start:
{
if (lean_obj_tag(v_x_2009_) == 0)
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_box(0);
return v___x_2010_;
}
else
{
lean_object* v_key_2011_; lean_object* v_value_2012_; lean_object* v_tail_2013_; uint8_t v___x_2014_; 
v_key_2011_ = lean_ctor_get(v_x_2009_, 0);
v_value_2012_ = lean_ctor_get(v_x_2009_, 1);
v_tail_2013_ = lean_ctor_get(v_x_2009_, 2);
v___x_2014_ = l_Lean_ExprStructEq_beq(v_key_2011_, v_a_2008_);
if (v___x_2014_ == 0)
{
v_x_2009_ = v_tail_2013_;
goto _start;
}
else
{
lean_object* v___x_2016_; 
lean_inc(v_value_2012_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_value_2012_);
return v___x_2016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_2017_, lean_object* v_x_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2017_, v_x_2018_);
lean_dec(v_x_2018_);
lean_dec_ref(v_a_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_buckets_2022_; lean_object* v___x_2023_; uint64_t v___x_2024_; uint64_t v___x_2025_; uint64_t v___x_2026_; uint64_t v_fold_2027_; uint64_t v___x_2028_; uint64_t v___x_2029_; uint64_t v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; size_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_buckets_2022_ = lean_ctor_get(v_m_2020_, 1);
v___x_2023_ = lean_array_get_size(v_buckets_2022_);
v___x_2024_ = l_Lean_ExprStructEq_hash(v_a_2021_);
v___x_2025_ = 32ULL;
v___x_2026_ = lean_uint64_shift_right(v___x_2024_, v___x_2025_);
v_fold_2027_ = lean_uint64_xor(v___x_2024_, v___x_2026_);
v___x_2028_ = 16ULL;
v___x_2029_ = lean_uint64_shift_right(v_fold_2027_, v___x_2028_);
v___x_2030_ = lean_uint64_xor(v_fold_2027_, v___x_2029_);
v___x_2031_ = lean_uint64_to_usize(v___x_2030_);
v___x_2032_ = lean_usize_of_nat(v___x_2023_);
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_sub(v___x_2032_, v___x_2033_);
v___x_2035_ = lean_usize_land(v___x_2031_, v___x_2034_);
v___x_2036_ = lean_array_uget_borrowed(v_buckets_2022_, v___x_2035_);
v___x_2037_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2021_, v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2038_, v_a_2039_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_m_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2041_, lean_object* v_x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_apply_1(v_x_2042_, lean_box(0));
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_2048_, v_x_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2053_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = l_Lean_interruptExceptionId;
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___x_2054_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_2061_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = l_Lean_maxRecDepthErrorMessage;
v___x_2068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_2070_ = l_Lean_MessageData_ofFormat(v___x_2069_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_2072_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_2073_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v___x_2071_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_ref_2074_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2079_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object* v_x_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___y_2088_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; uint8_t v___y_2101_; uint8_t v___y_2102_; uint16_t v___y_2103_; lean_object* v_toCold_2108_; lean_object* v_currRecDepth_2109_; lean_object* v_ref_2110_; uint16_t v_optionFlags_2111_; uint8_t v_suppressElabErrors_2112_; uint8_t v_isRecordingDeps_2113_; lean_object* v_maxRecDepth_2114_; lean_object* v_cancelTk_x3f_2115_; 
v_toCold_2108_ = lean_ctor_get(v___y_2084_, 0);
v_currRecDepth_2109_ = lean_ctor_get(v___y_2084_, 1);
v_ref_2110_ = lean_ctor_get(v___y_2084_, 2);
v_optionFlags_2111_ = lean_ctor_get_uint16(v___y_2084_, sizeof(void*)*3);
v_suppressElabErrors_2112_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2113_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*3 + 3);
v_maxRecDepth_2114_ = lean_ctor_get(v_toCold_2108_, 3);
v_cancelTk_x3f_2115_ = lean_ctor_get(v_toCold_2108_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2115_) == 1)
{
lean_object* v_val_2121_; uint8_t v___x_2122_; 
v_val_2121_ = lean_ctor_get(v_cancelTk_x3f_2115_, 0);
v___x_2122_ = l_IO_CancelToken_isSet(v_val_2121_);
if (v___x_2122_ == 0)
{
goto v___jp_2116_;
}
else
{
lean_object* v___x_2123_; lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_x_2082_);
v___x_2123_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
goto v___jp_2116_;
}
v___jp_2087_:
{
if (lean_obj_tag(v___y_2088_) == 0)
{
return v___y_2088_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_a_2089_ = lean_ctor_get(v___y_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___y_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___y_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___y_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
v___jp_2097_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_add(v___y_2100_, v___x_2104_);
lean_inc_ref(v___y_2099_);
v___x_2106_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2106_, 0, v___y_2099_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
lean_ctor_set(v___x_2106_, 2, v___y_2098_);
lean_ctor_set_uint16(v___x_2106_, sizeof(void*)*3, v___y_2103_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*3 + 2, v___y_2102_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*3 + 3, v___y_2101_);
lean_inc(v___y_2085_);
lean_inc(v___y_2083_);
v___x_2107_ = lean_apply_4(v_x_2082_, v___y_2083_, v___x_2106_, v___y_2085_, lean_box(0));
v___y_2088_ = v___x_2107_;
goto v___jp_2087_;
}
v___jp_2116_:
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = lean_nat_dec_eq(v_maxRecDepth_2114_, v___x_2117_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_nat_dec_eq(v_currRecDepth_2109_, v_maxRecDepth_2114_);
if (v___x_2119_ == 0)
{
lean_inc(v_ref_2110_);
v___y_2098_ = v_ref_2110_;
v___y_2099_ = v_toCold_2108_;
v___y_2100_ = v_currRecDepth_2109_;
v___y_2101_ = v_isRecordingDeps_2113_;
v___y_2102_ = v_suppressElabErrors_2112_;
v___y_2103_ = v_optionFlags_2111_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2120_; 
lean_dec_ref(v_x_2082_);
lean_inc(v_ref_2110_);
v___x_2120_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2110_);
v___y_2088_ = v___x_2120_;
goto v___jp_2087_;
}
}
else
{
lean_inc(v_ref_2110_);
v___y_2098_ = v_ref_2110_;
v___y_2099_ = v_toCold_2108_;
v___y_2100_ = v_currRecDepth_2109_;
v___y_2101_ = v_isRecordingDeps_2113_;
v___y_2102_ = v_suppressElabErrors_2112_;
v___y_2103_ = v_optionFlags_2111_;
goto v___jp_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_2138_, lean_object* v_x_2139_){
_start:
{
if (lean_obj_tag(v_x_2139_) == 0)
{
return v_x_2138_;
}
else
{
lean_object* v_key_2140_; lean_object* v_value_2141_; lean_object* v_tail_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2165_; 
v_key_2140_ = lean_ctor_get(v_x_2139_, 0);
v_value_2141_ = lean_ctor_get(v_x_2139_, 1);
v_tail_2142_ = lean_ctor_get(v_x_2139_, 2);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_2139_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2144_ = v_x_2139_;
v_isShared_2145_ = v_isSharedCheck_2165_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_tail_2142_);
lean_inc(v_value_2141_);
lean_inc(v_key_2140_);
lean_dec(v_x_2139_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2165_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; uint64_t v___x_2147_; uint64_t v___x_2148_; uint64_t v___x_2149_; uint64_t v_fold_2150_; uint64_t v___x_2151_; uint64_t v___x_2152_; uint64_t v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2146_ = lean_array_get_size(v_x_2138_);
v___x_2147_ = l_Lean_ExprStructEq_hash(v_key_2140_);
v___x_2148_ = 32ULL;
v___x_2149_ = lean_uint64_shift_right(v___x_2147_, v___x_2148_);
v_fold_2150_ = lean_uint64_xor(v___x_2147_, v___x_2149_);
v___x_2151_ = 16ULL;
v___x_2152_ = lean_uint64_shift_right(v_fold_2150_, v___x_2151_);
v___x_2153_ = lean_uint64_xor(v_fold_2150_, v___x_2152_);
v___x_2154_ = lean_uint64_to_usize(v___x_2153_);
v___x_2155_ = lean_usize_of_nat(v___x_2146_);
v___x_2156_ = ((size_t)1ULL);
v___x_2157_ = lean_usize_sub(v___x_2155_, v___x_2156_);
v___x_2158_ = lean_usize_land(v___x_2154_, v___x_2157_);
v___x_2159_ = lean_array_uget_borrowed(v_x_2138_, v___x_2158_);
lean_inc(v___x_2159_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 2, v___x_2159_);
v___x_2161_ = v___x_2144_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_key_2140_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_value_2141_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_array_uset(v_x_2138_, v___x_2158_, v___x_2161_);
v_x_2138_ = v___x_2162_;
v_x_2139_ = v_tail_2142_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_2166_, lean_object* v_source_2167_, lean_object* v_target_2168_){
_start:
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = lean_array_get_size(v_source_2167_);
v___x_2170_ = lean_nat_dec_lt(v_i_2166_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_dec_ref(v_source_2167_);
lean_dec(v_i_2166_);
return v_target_2168_;
}
else
{
lean_object* v_es_2171_; lean_object* v___x_2172_; lean_object* v_source_2173_; lean_object* v_target_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_es_2171_ = lean_array_fget(v_source_2167_, v_i_2166_);
v___x_2172_ = lean_box(0);
v_source_2173_ = lean_array_fset(v_source_2167_, v_i_2166_, v___x_2172_);
v_target_2174_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_2168_, v_es_2171_);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_add(v_i_2166_, v___x_2175_);
lean_dec(v_i_2166_);
v_i_2166_ = v___x_2176_;
v_source_2167_ = v_source_2173_;
v_target_2168_ = v_target_2174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_nbuckets_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2179_ = lean_array_get_size(v_data_2178_);
v___x_2180_ = lean_unsigned_to_nat(2u);
v_nbuckets_2181_ = lean_nat_mul(v___x_2179_, v___x_2180_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_mk_array(v_nbuckets_2181_, v___x_2183_);
v___x_2185_ = lean_array_propagate_mark(v_data_2178_, v___x_2184_);
v___x_2186_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_2182_, v_data_2178_, v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_2187_, lean_object* v_b_2188_, lean_object* v_x_2189_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 0)
{
lean_dec(v_b_2188_);
lean_dec_ref(v_a_2187_);
return v_x_2189_;
}
else
{
lean_object* v_key_2190_; lean_object* v_value_2191_; lean_object* v_tail_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2204_; 
v_key_2190_ = lean_ctor_get(v_x_2189_, 0);
v_value_2191_ = lean_ctor_get(v_x_2189_, 1);
v_tail_2192_ = lean_ctor_get(v_x_2189_, 2);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_x_2189_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2194_ = v_x_2189_;
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_tail_2192_);
lean_inc(v_value_2191_);
lean_inc(v_key_2190_);
lean_dec(v_x_2189_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
uint8_t v___x_2196_; 
v___x_2196_ = l_Lean_ExprStructEq_beq(v_key_2190_, v_a_2187_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2187_, v_b_2188_, v_tail_2192_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 2, v___x_2197_);
v___x_2199_ = v___x_2194_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_key_2190_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_value_2191_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
else
{
lean_object* v___x_2202_; 
lean_dec(v_value_2191_);
lean_dec(v_key_2190_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v_b_2188_);
lean_ctor_set(v___x_2194_, 0, v_a_2187_);
v___x_2202_ = v___x_2194_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2187_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_b_2188_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_tail_2192_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_2205_, lean_object* v_x_2206_){
_start:
{
if (lean_obj_tag(v_x_2206_) == 0)
{
uint8_t v___x_2207_; 
v___x_2207_ = 0;
return v___x_2207_;
}
else
{
lean_object* v_key_2208_; lean_object* v_tail_2209_; uint8_t v___x_2210_; 
v_key_2208_ = lean_ctor_get(v_x_2206_, 0);
v_tail_2209_ = lean_ctor_get(v_x_2206_, 2);
v___x_2210_ = l_Lean_ExprStructEq_beq(v_key_2208_, v_a_2205_);
if (v___x_2210_ == 0)
{
v_x_2206_ = v_tail_2209_;
goto _start;
}
else
{
return v___x_2210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_2212_, lean_object* v_x_2213_){
_start:
{
uint8_t v_res_2214_; lean_object* v_r_2215_; 
v_res_2214_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2212_, v_x_2213_);
lean_dec(v_x_2213_);
lean_dec_ref(v_a_2212_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object* v_m_2216_, lean_object* v_a_2217_, lean_object* v_b_2218_){
_start:
{
lean_object* v_size_2219_; lean_object* v_buckets_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2263_; 
v_size_2219_ = lean_ctor_get(v_m_2216_, 0);
v_buckets_2220_ = lean_ctor_get(v_m_2216_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_m_2216_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2222_ = v_m_2216_;
v_isShared_2223_ = v_isSharedCheck_2263_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_buckets_2220_);
lean_inc(v_size_2219_);
lean_dec(v_m_2216_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2263_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; uint64_t v___x_2225_; uint64_t v___x_2226_; uint64_t v___x_2227_; uint64_t v_fold_2228_; uint64_t v___x_2229_; uint64_t v___x_2230_; uint64_t v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v_bkt_2237_; uint8_t v___x_2238_; 
v___x_2224_ = lean_array_get_size(v_buckets_2220_);
v___x_2225_ = l_Lean_ExprStructEq_hash(v_a_2217_);
v___x_2226_ = 32ULL;
v___x_2227_ = lean_uint64_shift_right(v___x_2225_, v___x_2226_);
v_fold_2228_ = lean_uint64_xor(v___x_2225_, v___x_2227_);
v___x_2229_ = 16ULL;
v___x_2230_ = lean_uint64_shift_right(v_fold_2228_, v___x_2229_);
v___x_2231_ = lean_uint64_xor(v_fold_2228_, v___x_2230_);
v___x_2232_ = lean_uint64_to_usize(v___x_2231_);
v___x_2233_ = lean_usize_of_nat(v___x_2224_);
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_sub(v___x_2233_, v___x_2234_);
v___x_2236_ = lean_usize_land(v___x_2232_, v___x_2235_);
v_bkt_2237_ = lean_array_uget_borrowed(v_buckets_2220_, v___x_2236_);
v___x_2238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2217_, v_bkt_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v_size_x27_2240_; lean_object* v___x_2241_; lean_object* v_buckets_x27_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2239_ = lean_unsigned_to_nat(1u);
v_size_x27_2240_ = lean_nat_add(v_size_2219_, v___x_2239_);
lean_dec(v_size_2219_);
lean_inc(v_bkt_2237_);
v___x_2241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2217_);
lean_ctor_set(v___x_2241_, 1, v_b_2218_);
lean_ctor_set(v___x_2241_, 2, v_bkt_2237_);
v_buckets_x27_2242_ = lean_array_uset(v_buckets_2220_, v___x_2236_, v___x_2241_);
v___x_2243_ = lean_unsigned_to_nat(4u);
v___x_2244_ = lean_nat_mul(v_size_x27_2240_, v___x_2243_);
v___x_2245_ = lean_unsigned_to_nat(3u);
v___x_2246_ = lean_nat_div(v___x_2244_, v___x_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_array_get_size(v_buckets_x27_2242_);
v___x_2248_ = lean_nat_dec_le(v___x_2246_, v___x_2247_);
lean_dec(v___x_2246_);
if (v___x_2248_ == 0)
{
lean_object* v_val_2249_; lean_object* v___x_2251_; 
v_val_2249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_2242_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v_val_2249_);
lean_ctor_set(v___x_2222_, 0, v_size_x27_2240_);
v___x_2251_ = v___x_2222_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_size_x27_2240_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_val_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
else
{
lean_object* v___x_2254_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v_buckets_x27_2242_);
lean_ctor_set(v___x_2222_, 0, v_size_x27_2240_);
v___x_2254_ = v___x_2222_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_size_x27_2240_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_buckets_x27_2242_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v_buckets_x27_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
lean_inc(v_bkt_2237_);
v___x_2256_ = lean_box(0);
v_buckets_x27_2257_ = lean_array_uset(v_buckets_2220_, v___x_2236_, v___x_2256_);
v___x_2258_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2217_, v_b_2218_, v_bkt_2237_);
v___x_2259_ = lean_array_uset(v_buckets_x27_2257_, v___x_2236_, v___x_2258_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___x_2259_);
v___x_2261_ = v___x_2222_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_size_2219_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v___x_2259_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object* v_a_2264_, lean_object* v_e_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2268_ = lean_st_ref_take(v_a_2264_);
v___x_2269_ = lean_box(0);
v___x_2270_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2268_, v_e_2265_, v_a_2266_);
v___x_2271_ = lean_st_ref_put(v_a_2264_, v___x_2270_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2272_, lean_object* v_e_2273_, lean_object* v_a_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2272_, v_e_2273_, v_a_2274_);
lean_dec(v_a_2272_);
return v_res_2276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2278_; lean_object* v_dummy_2279_; 
v___x_2278_ = lean_box(0);
v_dummy_2279_ = l_Lean_Expr_sort___override(v___x_2278_);
return v_dummy_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object* v_pre_2280_, lean_object* v_post_2281_, size_t v_sz_2282_, size_t v_i_2283_, lean_object* v_bs_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_usize_dec_lt(v_i_2283_, v_sz_2282_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref(v_post_2281_);
lean_dec_ref(v_pre_2280_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_bs_2284_);
return v___x_2290_;
}
else
{
lean_object* v_v_2291_; lean_object* v___x_2292_; lean_object* v_bs_x27_2293_; lean_object* v___x_2294_; 
v_v_2291_ = lean_array_uget(v_bs_2284_, v_i_2283_);
v___x_2292_ = lean_unsigned_to_nat(0u);
v_bs_x27_2293_ = lean_array_uset(v_bs_2284_, v_i_2283_, v___x_2292_);
lean_inc_ref(v_post_2281_);
lean_inc_ref(v_pre_2280_);
v___x_2294_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2280_, v_post_2281_, v_v_2291_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; size_t v___x_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = ((size_t)1ULL);
v___x_2297_ = lean_usize_add(v_i_2283_, v___x_2296_);
v___x_2298_ = lean_array_uset(v_bs_x27_2293_, v_i_2283_, v_a_2295_);
v_i_2283_ = v___x_2297_;
v_bs_2284_ = v___x_2298_;
goto _start;
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v_bs_x27_2293_);
lean_dec_ref(v_post_2281_);
lean_dec_ref(v_pre_2280_);
v_a_2300_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2294_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2294_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object* v_pre_2308_, lean_object* v_post_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 5)
{
lean_object* v_fn_2317_; lean_object* v_arg_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_fn_2317_ = lean_ctor_get(v_x_2310_, 0);
lean_inc_ref(v_fn_2317_);
v_arg_2318_ = lean_ctor_get(v_x_2310_, 1);
lean_inc_ref(v_arg_2318_);
lean_dec_ref_known(v_x_2310_, 2);
v___x_2319_ = lean_array_set(v_x_2311_, v_x_2312_, v_arg_2318_);
v___x_2320_ = lean_unsigned_to_nat(1u);
v___x_2321_ = lean_nat_sub(v_x_2312_, v___x_2320_);
lean_dec(v_x_2312_);
v_x_2310_ = v_fn_2317_;
v_x_2311_ = v___x_2319_;
v_x_2312_ = v___x_2321_;
goto _start;
}
else
{
lean_object* v___x_2323_; 
lean_dec(v_x_2312_);
lean_inc_ref(v_post_2309_);
lean_inc_ref(v_pre_2308_);
v___x_2323_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2308_, v_post_2309_, v_x_2310_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; size_t v_sz_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v_sz_2325_ = lean_array_size(v_x_2311_);
v___x_2326_ = ((size_t)0ULL);
lean_inc_ref(v_post_2309_);
lean_inc_ref(v_pre_2308_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2308_, v_post_2309_, v_sz_2325_, v___x_2326_, v_x_2311_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = l_Lean_mkAppN(v_a_2324_, v_a_2328_);
lean_dec(v_a_2328_);
v___x_2330_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2308_, v_post_2309_, v___x_2329_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2330_;
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_a_2324_);
lean_dec_ref(v_post_2309_);
lean_dec_ref(v_pre_2308_);
v_a_2331_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2327_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2327_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_dec_ref(v_x_2311_);
lean_dec_ref(v_post_2309_);
lean_dec_ref(v_pre_2308_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object* v___x_2339_, lean_object* v_pre_2340_, lean_object* v_e_2341_, lean_object* v_post_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Core_checkSystem(v___x_2339_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v___x_2348_; 
lean_dec_ref_known(v___x_2347_, 1);
lean_inc_ref(v_pre_2340_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc_ref(v_e_2341_);
v___x_2348_ = lean_apply_4(v_pre_2340_, v_e_2341_, v___y_2344_, v___y_2345_, lean_box(0));
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2464_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2464_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2464_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___y_2354_; 
switch(lean_obj_tag(v_a_2349_))
{
case 0:
{
lean_object* v_e_2454_; lean_object* v___x_2456_; 
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_e_2341_);
lean_dec_ref(v_pre_2340_);
v_e_2454_ = lean_ctor_get(v_a_2349_, 0);
lean_inc_ref(v_e_2454_);
lean_dec_ref_known(v_a_2349_, 1);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v_e_2454_);
v___x_2456_ = v___x_2351_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_e_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
case 1:
{
lean_object* v_e_2458_; lean_object* v___x_2459_; 
lean_del_object(v___x_2351_);
lean_dec_ref(v_e_2341_);
v_e_2458_ = lean_ctor_get(v_a_2349_, 0);
lean_inc_ref(v_e_2458_);
lean_dec_ref_known(v_a_2349_, 1);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_e_2458_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v_a_2460_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2461_;
}
else
{
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2459_;
}
}
default: 
{
lean_object* v_e_x3f_2462_; 
lean_del_object(v___x_2351_);
v_e_x3f_2462_ = lean_ctor_get(v_a_2349_, 0);
lean_inc(v_e_x3f_2462_);
lean_dec_ref_known(v_a_2349_, 1);
if (lean_obj_tag(v_e_x3f_2462_) == 0)
{
v___y_2354_ = v_e_2341_;
goto v___jp_2353_;
}
else
{
lean_object* v_val_2463_; 
lean_dec_ref(v_e_2341_);
v_val_2463_ = lean_ctor_get(v_e_x3f_2462_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v_e_x3f_2462_, 1);
v___y_2354_ = v_val_2463_;
goto v___jp_2353_;
}
}
}
v___jp_2353_:
{
switch(lean_obj_tag(v___y_2354_))
{
case 7:
{
lean_object* v_binderName_2355_; lean_object* v_binderType_2356_; lean_object* v_body_2357_; uint8_t v_binderInfo_2358_; lean_object* v___x_2359_; 
v_binderName_2355_ = lean_ctor_get(v___y_2354_, 0);
v_binderType_2356_ = lean_ctor_get(v___y_2354_, 1);
v_body_2357_ = lean_ctor_get(v___y_2354_, 2);
v_binderInfo_2358_ = lean_ctor_get_uint8(v___y_2354_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2356_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2359_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_binderType_2356_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
lean_inc_ref(v_body_2357_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2361_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_body_2357_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; size_t v___x_2363_; size_t v___x_2364_; uint8_t v___x_2365_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = lean_ptr_addr(v_binderType_2356_);
v___x_2364_ = lean_ptr_addr(v_a_2360_);
v___x_2365_ = lean_usize_dec_eq(v___x_2363_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_inc(v_binderName_2355_);
lean_dec_ref_known(v___y_2354_, 3);
v___x_2366_ = l_Lean_Expr_forallE___override(v_binderName_2355_, v_a_2360_, v_a_2362_, v_binderInfo_2358_);
v___x_2367_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2366_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2367_;
}
else
{
size_t v___x_2368_; size_t v___x_2369_; uint8_t v___x_2370_; 
v___x_2368_ = lean_ptr_addr(v_body_2357_);
v___x_2369_ = lean_ptr_addr(v_a_2362_);
v___x_2370_ = lean_usize_dec_eq(v___x_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_inc(v_binderName_2355_);
lean_dec_ref_known(v___y_2354_, 3);
v___x_2371_ = l_Lean_Expr_forallE___override(v_binderName_2355_, v_a_2360_, v_a_2362_, v_binderInfo_2358_);
v___x_2372_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2371_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2372_;
}
else
{
uint8_t v___x_2373_; 
v___x_2373_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2358_, v_binderInfo_2358_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_inc(v_binderName_2355_);
lean_dec_ref_known(v___y_2354_, 3);
v___x_2374_ = l_Lean_Expr_forallE___override(v_binderName_2355_, v_a_2360_, v_a_2362_, v_binderInfo_2358_);
v___x_2375_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2374_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; 
lean_dec(v_a_2362_);
lean_dec(v_a_2360_);
v___x_2376_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___y_2354_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2376_;
}
}
}
}
else
{
lean_dec(v_a_2360_);
lean_dec_ref_known(v___y_2354_, 3);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2361_;
}
}
else
{
lean_dec_ref_known(v___y_2354_, 3);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2359_;
}
}
case 6:
{
lean_object* v_binderName_2377_; lean_object* v_binderType_2378_; lean_object* v_body_2379_; uint8_t v_binderInfo_2380_; lean_object* v___x_2381_; 
v_binderName_2377_ = lean_ctor_get(v___y_2354_, 0);
v_binderType_2378_ = lean_ctor_get(v___y_2354_, 1);
v_body_2379_ = lean_ctor_get(v___y_2354_, 2);
v_binderInfo_2380_ = lean_ctor_get_uint8(v___y_2354_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2378_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2381_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_binderType_2378_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
lean_inc_ref(v_body_2379_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2383_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_body_2379_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; size_t v___x_2385_; size_t v___x_2386_; uint8_t v___x_2387_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = lean_ptr_addr(v_binderType_2378_);
v___x_2386_ = lean_ptr_addr(v_a_2382_);
v___x_2387_ = lean_usize_dec_eq(v___x_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_inc(v_binderName_2377_);
lean_dec_ref_known(v___y_2354_, 3);
v___x_2388_ = l_Lean_Expr_lam___override(v_binderName_2377_, v_a_2382_, v_a_2384_, v_binderInfo_2380_);
v___x_2389_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2388_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2389_;
}
else
{
size_t v___x_2390_; size_t v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = lean_ptr_addr(v_body_2379_);
v___x_2391_ = lean_ptr_addr(v_a_2384_);
v___x_2392_ = lean_usize_dec_eq(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_inc(v_binderName_2377_);
lean_dec_ref_known(v___y_2354_, 3);
v___x_2393_ = l_Lean_Expr_lam___override(v_binderName_2377_, v_a_2382_, v_a_2384_, v_binderInfo_2380_);
v___x_2394_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2393_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2394_;
}
else
{
uint8_t v___x_2395_; 
v___x_2395_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2380_, v_binderInfo_2380_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_inc(v_binderName_2377_);
lean_dec_ref_known(v___y_2354_, 3);
v___x_2396_ = l_Lean_Expr_lam___override(v_binderName_2377_, v_a_2382_, v_a_2384_, v_binderInfo_2380_);
v___x_2397_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2396_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2397_;
}
else
{
lean_object* v___x_2398_; 
lean_dec(v_a_2384_);
lean_dec(v_a_2382_);
v___x_2398_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___y_2354_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2398_;
}
}
}
}
else
{
lean_dec(v_a_2382_);
lean_dec_ref_known(v___y_2354_, 3);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2383_;
}
}
else
{
lean_dec_ref_known(v___y_2354_, 3);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2381_;
}
}
case 8:
{
lean_object* v_declName_2399_; lean_object* v_type_2400_; lean_object* v_value_2401_; lean_object* v_body_2402_; uint8_t v_nondep_2403_; lean_object* v___x_2404_; 
v_declName_2399_ = lean_ctor_get(v___y_2354_, 0);
v_type_2400_ = lean_ctor_get(v___y_2354_, 1);
v_value_2401_ = lean_ctor_get(v___y_2354_, 2);
v_body_2402_ = lean_ctor_get(v___y_2354_, 3);
v_nondep_2403_ = lean_ctor_get_uint8(v___y_2354_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2400_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2404_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_type_2400_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
lean_inc_ref(v_value_2401_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2406_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_value_2401_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
lean_inc_ref(v_body_2402_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2408_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_body_2402_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; size_t v___x_2410_; size_t v___x_2411_; uint8_t v___x_2412_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = lean_ptr_addr(v_type_2400_);
v___x_2411_ = lean_ptr_addr(v_a_2405_);
v___x_2412_ = lean_usize_dec_eq(v___x_2410_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_inc(v_declName_2399_);
lean_dec_ref_known(v___y_2354_, 4);
v___x_2413_ = l_Lean_Expr_letE___override(v_declName_2399_, v_a_2405_, v_a_2407_, v_a_2409_, v_nondep_2403_);
v___x_2414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2413_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2414_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; uint8_t v___x_2417_; 
v___x_2415_ = lean_ptr_addr(v_value_2401_);
v___x_2416_ = lean_ptr_addr(v_a_2407_);
v___x_2417_ = lean_usize_dec_eq(v___x_2415_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_inc(v_declName_2399_);
lean_dec_ref_known(v___y_2354_, 4);
v___x_2418_ = l_Lean_Expr_letE___override(v_declName_2399_, v_a_2405_, v_a_2407_, v_a_2409_, v_nondep_2403_);
v___x_2419_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2418_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2419_;
}
else
{
size_t v___x_2420_; size_t v___x_2421_; uint8_t v___x_2422_; 
v___x_2420_ = lean_ptr_addr(v_body_2402_);
v___x_2421_ = lean_ptr_addr(v_a_2409_);
v___x_2422_ = lean_usize_dec_eq(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_inc(v_declName_2399_);
lean_dec_ref_known(v___y_2354_, 4);
v___x_2423_ = l_Lean_Expr_letE___override(v_declName_2399_, v_a_2405_, v_a_2407_, v_a_2409_, v_nondep_2403_);
v___x_2424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2423_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; 
lean_dec(v_a_2409_);
lean_dec(v_a_2407_);
lean_dec(v_a_2405_);
v___x_2425_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___y_2354_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2425_;
}
}
}
}
else
{
lean_dec(v_a_2407_);
lean_dec(v_a_2405_);
lean_dec_ref_known(v___y_2354_, 4);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2408_;
}
}
else
{
lean_dec(v_a_2405_);
lean_dec_ref_known(v___y_2354_, 4);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2406_;
}
}
else
{
lean_dec_ref_known(v___y_2354_, 4);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2404_;
}
}
case 5:
{
lean_object* v_dummy_2426_; lean_object* v_nargs_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_dummy_2426_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_2427_ = l_Lean_Expr_getAppNumArgs(v___y_2354_);
lean_inc(v_nargs_2427_);
v___x_2428_ = lean_mk_array(v_nargs_2427_, v_dummy_2426_);
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = lean_nat_sub(v_nargs_2427_, v___x_2429_);
lean_dec(v_nargs_2427_);
v___x_2431_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2340_, v_post_2342_, v___y_2354_, v___x_2428_, v___x_2430_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2431_;
}
case 10:
{
lean_object* v_data_2432_; lean_object* v_expr_2433_; lean_object* v___x_2434_; 
v_data_2432_ = lean_ctor_get(v___y_2354_, 0);
v_expr_2433_ = lean_ctor_get(v___y_2354_, 1);
lean_inc_ref(v_expr_2433_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_expr_2433_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; size_t v___x_2436_; size_t v___x_2437_; uint8_t v___x_2438_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = lean_ptr_addr(v_expr_2433_);
v___x_2437_ = lean_ptr_addr(v_a_2435_);
v___x_2438_ = lean_usize_dec_eq(v___x_2436_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_inc(v_data_2432_);
lean_dec_ref_known(v___y_2354_, 2);
v___x_2439_ = l_Lean_Expr_mdata___override(v_data_2432_, v_a_2435_);
v___x_2440_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2439_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; 
lean_dec(v_a_2435_);
v___x_2441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___y_2354_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2441_;
}
}
else
{
lean_dec_ref_known(v___y_2354_, 2);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2434_;
}
}
case 11:
{
lean_object* v_typeName_2442_; lean_object* v_idx_2443_; lean_object* v_struct_2444_; lean_object* v___x_2445_; 
v_typeName_2442_ = lean_ctor_get(v___y_2354_, 0);
v_idx_2443_ = lean_ctor_get(v___y_2354_, 1);
v_struct_2444_ = lean_ctor_get(v___y_2354_, 2);
lean_inc_ref(v_struct_2444_);
lean_inc_ref(v_post_2342_);
lean_inc_ref(v_pre_2340_);
v___x_2445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2340_, v_post_2342_, v_struct_2444_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; size_t v___x_2447_; size_t v___x_2448_; uint8_t v___x_2449_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2447_ = lean_ptr_addr(v_struct_2444_);
v___x_2448_ = lean_ptr_addr(v_a_2446_);
v___x_2449_ = lean_usize_dec_eq(v___x_2447_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_inc(v_idx_2443_);
lean_inc(v_typeName_2442_);
lean_dec_ref_known(v___y_2354_, 3);
v___x_2450_ = l_Lean_Expr_proj___override(v_typeName_2442_, v_idx_2443_, v_a_2446_);
v___x_2451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___x_2450_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2451_;
}
else
{
lean_object* v___x_2452_; 
lean_dec(v_a_2446_);
v___x_2452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___y_2354_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2452_;
}
}
else
{
lean_dec_ref_known(v___y_2354_, 3);
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_pre_2340_);
return v___x_2445_;
}
}
default: 
{
lean_object* v___x_2453_; 
v___x_2453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2340_, v_post_2342_, v___y_2354_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2453_;
}
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_e_2341_);
lean_dec_ref(v_pre_2340_);
v_a_2465_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2348_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2348_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_post_2342_);
lean_dec_ref(v_e_2341_);
lean_dec_ref(v_pre_2340_);
v_a_2473_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2347_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2347_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2481_, lean_object* v_pre_2482_, lean_object* v_e_2483_, lean_object* v_post_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_2481_, v_pre_2482_, v_e_2483_, v_post_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object* v_pre_2490_, lean_object* v_post_2491_, lean_object* v_e_2492_, lean_object* v_a_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_inc(v_a_2493_);
v___x_2497_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2497_, 0, lean_box(0));
lean_closure_set(v___x_2497_, 1, lean_box(0));
lean_closure_set(v___x_2497_, 2, v_a_2493_);
v___x_2498_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___x_2497_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2530_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2530_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2530_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_2499_, v_e_2492_);
lean_dec(v_a_2499_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v___x_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; 
lean_del_object(v___x_2501_);
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_2492_);
v___f_2505_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2505_, 0, v___x_2504_);
lean_closure_set(v___f_2505_, 1, v_pre_2490_);
lean_closure_set(v___f_2505_, 2, v_e_2492_);
lean_closure_set(v___f_2505_, 3, v_post_2491_);
v___x_2506_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2505_, v_a_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc_n(v_a_2507_, 2);
lean_dec_ref_known(v___x_2506_, 1);
lean_inc(v_a_2493_);
v___f_2508_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2508_, 0, v_a_2493_);
lean_closure_set(v___f_2508_, 1, v_e_2492_);
lean_closure_set(v___f_2508_, 2, v_a_2507_);
v___x_2509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___f_2508_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2509_, 0);
lean_dec(v_unused_2517_);
v___x_2511_ = v___x_2509_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v___x_2509_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_a_2507_);
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2507_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_a_2507_);
v_a_2518_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2509_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2509_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_dec_ref(v_e_2492_);
return v___x_2506_;
}
}
else
{
lean_object* v_val_2526_; lean_object* v___x_2528_; 
lean_dec_ref(v_e_2492_);
lean_dec_ref(v_post_2491_);
lean_dec_ref(v_pre_2490_);
v_val_2526_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_val_2526_);
lean_dec_ref_known(v___x_2503_, 1);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v_val_2526_);
v___x_2528_ = v___x_2501_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_val_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_e_2492_);
lean_dec_ref(v_post_2491_);
lean_dec_ref(v_pre_2490_);
v_a_2531_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2498_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2498_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object* v_pre_2539_, lean_object* v_post_2540_, lean_object* v_e_2541_, lean_object* v_a_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; 
lean_inc_ref(v_post_2540_);
lean_inc(v___y_2544_);
lean_inc_ref(v___y_2543_);
lean_inc_ref(v_e_2541_);
v___x_2546_ = lean_apply_4(v_post_2540_, v_e_2541_, v___y_2543_, v___y_2544_, lean_box(0));
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2565_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2565_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2565_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
switch(lean_obj_tag(v_a_2547_))
{
case 0:
{
lean_object* v_e_2551_; lean_object* v___x_2553_; 
lean_dec_ref(v_e_2541_);
lean_dec_ref(v_post_2540_);
lean_dec_ref(v_pre_2539_);
v_e_2551_ = lean_ctor_get(v_a_2547_, 0);
lean_inc_ref(v_e_2551_);
lean_dec_ref_known(v_a_2547_, 1);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v_e_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_e_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
case 1:
{
lean_object* v_e_2555_; lean_object* v___x_2556_; 
lean_del_object(v___x_2549_);
lean_dec_ref(v_e_2541_);
v_e_2555_ = lean_ctor_get(v_a_2547_, 0);
lean_inc_ref(v_e_2555_);
lean_dec_ref_known(v_a_2547_, 1);
v___x_2556_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2539_, v_post_2540_, v_e_2555_, v_a_2542_, v___y_2543_, v___y_2544_);
return v___x_2556_;
}
default: 
{
lean_object* v_e_x3f_2557_; 
lean_dec_ref(v_post_2540_);
lean_dec_ref(v_pre_2539_);
v_e_x3f_2557_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_e_x3f_2557_);
lean_dec_ref_known(v_a_2547_, 1);
if (lean_obj_tag(v_e_x3f_2557_) == 0)
{
lean_object* v___x_2559_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v_e_2541_);
v___x_2559_ = v___x_2549_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_e_2541_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
else
{
lean_object* v_val_2561_; lean_object* v___x_2563_; 
lean_dec_ref(v_e_2541_);
v_val_2561_ = lean_ctor_get(v_e_x3f_2557_, 0);
lean_inc(v_val_2561_);
lean_dec_ref_known(v_e_x3f_2557_, 1);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v_val_2561_);
v___x_2563_ = v___x_2549_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_val_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v_e_2541_);
lean_dec_ref(v_post_2540_);
lean_dec_ref(v_pre_2539_);
v_a_2566_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2546_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2546_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2574_, lean_object* v_post_2575_, lean_object* v_e_2576_, lean_object* v_a_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2574_, v_post_2575_, v_e_2576_, v_a_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v_a_2577_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2582_, lean_object* v_post_2583_, lean_object* v_sz_2584_, lean_object* v_i_2585_, lean_object* v_bs_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
size_t v_sz_boxed_2591_; size_t v_i_boxed_2592_; lean_object* v_res_2593_; 
v_sz_boxed_2591_ = lean_unbox_usize(v_sz_2584_);
lean_dec(v_sz_2584_);
v_i_boxed_2592_ = lean_unbox_usize(v_i_2585_);
lean_dec(v_i_2585_);
v_res_2593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2582_, v_post_2583_, v_sz_boxed_2591_, v_i_boxed_2592_, v_bs_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_2594_, lean_object* v_post_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_, lean_object* v_x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2594_, v_post_2595_, v_x_2596_, v_x_2597_, v_x_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(lean_object* v_pre_2604_, lean_object* v_post_2605_, lean_object* v_e_2606_, lean_object* v_a_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2604_, v_post_2605_, v_e_2606_, v_a_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v_a_2607_);
return v_res_2611_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_unsigned_to_nat(16u);
v___x_2614_ = lean_mk_array(v___x_2613_, v___x_2612_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
v___x_2619_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2619_, 0, lean_box(0));
lean_closure_set(v___x_2619_, 1, lean_box(0));
lean_closure_set(v___x_2619_, 2, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object* v_input_2620_, lean_object* v_pre_2621_, lean_object* v_post_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_a_2628_; lean_object* v___x_2629_; 
v___x_2626_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_2627_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2626_, v___y_2623_, v___y_2624_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2621_, v_post_2622_, v_input_2620_, v_a_2628_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2631_, 0, lean_box(0));
lean_closure_set(v___x_2631_, 1, lean_box(0));
lean_closure_set(v___x_2631_, 2, v_a_2628_);
v___x_2632_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2631_, v___y_2623_, v___y_2624_);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; 
v_unused_2640_ = lean_ctor_get(v___x_2632_, 0);
lean_dec(v_unused_2640_);
v___x_2634_ = v___x_2632_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_dec(v___x_2632_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_a_2630_);
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2630_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
else
{
lean_dec(v_a_2628_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object* v_input_2641_, lean_object* v_pre_2642_, lean_object* v_post_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2641_, v_pre_2642_, v_post_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* v_e_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___f_2655_; lean_object* v___x_2656_; 
v___f_2655_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0));
v___x_2656_ = lean_find_expr(v___f_2655_, v_e_2651_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_e_2651_);
return v___x_2657_;
}
else
{
lean_object* v_pre_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; 
lean_dec_ref_known(v___x_2656_, 1);
v_pre_2658_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1));
v___f_2659_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2));
v___x_2660_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_e_2651_, v_pre_2658_, v___f_2659_, v_a_2652_, v_a_2653_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object* v_e_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2666_, lean_object* v_m_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2667_, v_a_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2670_, lean_object* v_m_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_2670_, v_m_2671_, v_a_2672_);
lean_dec_ref(v_a_2672_);
lean_dec_ref(v_m_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_2674_, lean_object* v_ref_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2675_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2680_, lean_object* v_ref_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2680_, v_ref_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_2703_, v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2710_, lean_object* v_m_2711_, lean_object* v_a_2712_, lean_object* v_b_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2711_, v_a_2712_, v_b_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_2715_, lean_object* v_a_2716_, lean_object* v_x_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2716_, v_x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2719_, lean_object* v_a_2720_, lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2719_, v_a_2720_, v_x_2721_);
lean_dec(v_x_2721_);
lean_dec_ref(v_a_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_2723_, lean_object* v_a_2724_, lean_object* v_x_2725_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_2724_, v_x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2727_, lean_object* v_a_2728_, lean_object* v_x_2729_){
_start:
{
uint8_t v_res_2730_; lean_object* v_r_2731_; 
v_res_2730_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_2727_, v_a_2728_, v_x_2729_);
lean_dec(v_x_2729_);
lean_dec_ref(v_a_2728_);
v_r_2731_ = lean_box(v_res_2730_);
return v_r_2731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_2732_, lean_object* v_data_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_data_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_2735_, lean_object* v_a_2736_, lean_object* v_b_2737_, lean_object* v_x_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_2736_, v_b_2737_, v_x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_2740_, lean_object* v_i_2741_, lean_object* v_source_2742_, lean_object* v_target_2743_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_2741_, v_source_2742_, v_target_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_2746_, v_x_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData___lam__0(lean_object* v_e_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2749_, v___y_2752_, v___y_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData___lam__0___boxed(lean_object* v_e_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_MVarId_eraseIrrelevantMData___lam__0(v_e_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData(lean_object* v_mvarId_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___f_2770_; lean_object* v___x_2771_; 
v___f_2770_ = ((lean_object*)(l_Lean_MVarId_eraseIrrelevantMData___closed__0));
v___x_2771_ = l_Lean_MVarId_transformTarget(v_mvarId_2764_, v___f_2770_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_eraseIrrelevantMData___boxed(lean_object* v_mvarId_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_MVarId_eraseIrrelevantMData(v_mvarId_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_Meta_Sym_foldProjs(v_e_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_Meta_Grind_foldProjs(v_e_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_2800_, lean_object* v_config_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_00___x40___internal___hyg_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = lean_grind_normalize(v_e_2800_, v_config_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
return v_res_2807_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2815_ = lean_box(0);
v___x_2816_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2817_ = l_Lean_mkConst(v___x_2816_, v___x_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_2818_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_2820_ = l_Lean_Expr_app___override(v___x_2819_, v_e_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_2821_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2822_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_2823_ = lean_unsigned_to_nat(1u);
v___x_2824_ = l_Lean_Expr_isAppOfArity(v_e_2821_, v___x_2822_, v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_2825_){
_start:
{
uint8_t v_res_2826_; lean_object* v_r_2827_; 
v_res_2826_ = l_Lean_Meta_Grind_isMatchCond(v_e_2825_);
lean_dec_ref(v_e_2825_);
v_r_2827_ = lean_box(v_res_2826_);
return v_r_2827_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = lean_box(0);
v___x_2834_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2835_ = l_Lean_mkConst(v___x_2834_, v___x_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_2838_ = l_Lean_Expr_app___override(v___x_2837_, v_e_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2840_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = l_Lean_Expr_isAppOfArity(v_e_2839_, v___x_2840_, v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_2843_){
_start:
{
uint8_t v_res_2844_; lean_object* v_r_2845_; 
v_res_2844_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_2843_);
lean_dec_ref(v_e_2843_);
v_r_2845_ = lean_box(v_res_2844_);
return v_r_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2854_; 
lean_inc_ref(v_e_2848_);
v___x_2854_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2848_, v_a_2849_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2868_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2868_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2868_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = l_Lean_Expr_cleanupAnnotations(v_a_2855_);
v___x_2860_ = l_Lean_Expr_isApp(v___x_2859_);
if (v___x_2860_ == 0)
{
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2857_);
lean_dec_ref(v_e_2848_);
goto v___jp_2851_;
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2861_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2859_);
v___x_2862_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2863_ = l_Lean_Expr_isConstOf(v___x_2861_, v___x_2862_);
lean_dec_ref(v___x_2861_);
if (v___x_2863_ == 0)
{
lean_del_object(v___x_2857_);
lean_dec_ref(v_e_2848_);
goto v___jp_2851_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_e_2848_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2864_);
v___x_2866_ = v___x_2857_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec_ref(v_e_2848_);
v_a_2869_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2854_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2854_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
v___jp_2851_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = ((lean_object*)(l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0));
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_2877_, v_a_2878_);
lean_dec(v_a_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_2881_, v_a_2886_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_2919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_2920_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_2921_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2918_, v___x_2919_, v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11____boxed(lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v___x_2928_; uint8_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_));
v___x_2929_ = 0;
v___x_2930_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2924_, v___x_2928_, v___x_2929_, v_a_2925_, v_a_2926_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_2931_, v_a_2932_, v_a_2933_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
lean_inc_ref(v_e_2936_);
v___x_2946_ = l_Lean_Expr_cleanupAnnotations(v_e_2936_);
v___x_2947_ = l_Lean_Expr_isApp(v___x_2946_);
if (v___x_2947_ == 0)
{
lean_dec_ref(v___x_2946_);
goto v___jp_2942_;
}
else
{
lean_object* v_arg_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v_arg_2948_ = lean_ctor_get(v___x_2946_, 1);
lean_inc_ref(v_arg_2948_);
v___x_2949_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2946_);
v___x_2950_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_2951_ = l_Lean_Expr_isConstOf(v___x_2949_, v___x_2950_);
lean_dec_ref(v___x_2949_);
if (v___x_2951_ == 0)
{
lean_dec_ref(v_arg_2948_);
goto v___jp_2942_;
}
else
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec_ref(v_e_2936_);
v___x_2952_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_2948_);
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
v___jp_2942_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_e_2936_);
v___x_2944_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* v_e_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_e_2963_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_object* v_00_u03b1_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_apply_1(v_x_2979_, lean_box(0));
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_x_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(v_00_u03b1_2987_, v_x_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v___y_3003_; uint8_t v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; uint16_t v___y_3016_; uint8_t v___y_3017_; lean_object* v___y_3018_; lean_object* v_toCold_3023_; lean_object* v_currRecDepth_3024_; lean_object* v_ref_3025_; uint16_t v_optionFlags_3026_; uint8_t v_suppressElabErrors_3027_; uint8_t v_isRecordingDeps_3028_; lean_object* v_maxRecDepth_3029_; lean_object* v_cancelTk_x3f_3030_; 
v_toCold_3023_ = lean_ctor_get(v___y_2999_, 0);
v_currRecDepth_3024_ = lean_ctor_get(v___y_2999_, 1);
v_ref_3025_ = lean_ctor_get(v___y_2999_, 2);
v_optionFlags_3026_ = lean_ctor_get_uint16(v___y_2999_, sizeof(void*)*3);
v_suppressElabErrors_3027_ = lean_ctor_get_uint8(v___y_2999_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3028_ = lean_ctor_get_uint8(v___y_2999_, sizeof(void*)*3 + 3);
v_maxRecDepth_3029_ = lean_ctor_get(v_toCold_3023_, 3);
v_cancelTk_x3f_3030_ = lean_ctor_get(v_toCold_3023_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3030_) == 1)
{
lean_object* v_val_3036_; uint8_t v___x_3037_; 
v_val_3036_ = lean_ctor_get(v_cancelTk_x3f_3030_, 0);
v___x_3037_ = l_IO_CancelToken_isSet(v_val_3036_);
if (v___x_3037_ == 0)
{
goto v___jp_3031_;
}
else
{
lean_object* v___x_3038_; lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v_x_2995_);
v___x_3038_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
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
else
{
goto v___jp_3031_;
}
v___jp_3002_:
{
if (lean_obj_tag(v___y_3003_) == 0)
{
return v___y_3003_;
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_a_3004_ = lean_ctor_get(v___y_3003_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___y_3003_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___y_3003_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___y_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
v___jp_3012_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3019_ = lean_unsigned_to_nat(1u);
v___x_3020_ = lean_nat_add(v___y_3018_, v___x_3019_);
lean_inc_ref(v___y_3015_);
v___x_3021_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3021_, 0, v___y_3015_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
lean_ctor_set(v___x_3021_, 2, v___y_3014_);
lean_ctor_set_uint16(v___x_3021_, sizeof(void*)*3, v___y_3016_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*3 + 2, v___y_3013_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*3 + 3, v___y_3017_);
lean_inc(v___y_3000_);
lean_inc(v___y_2998_);
lean_inc_ref(v___y_2997_);
lean_inc(v___y_2996_);
v___x_3022_ = lean_apply_6(v_x_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___x_3021_, v___y_3000_, lean_box(0));
v___y_3003_ = v___x_3022_;
goto v___jp_3002_;
}
v___jp_3031_:
{
lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = lean_nat_dec_eq(v_maxRecDepth_3029_, v___x_3032_);
if (v___x_3033_ == 0)
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_nat_dec_eq(v_currRecDepth_3024_, v_maxRecDepth_3029_);
if (v___x_3034_ == 0)
{
lean_inc(v_ref_3025_);
v___y_3013_ = v_suppressElabErrors_3027_;
v___y_3014_ = v_ref_3025_;
v___y_3015_ = v_toCold_3023_;
v___y_3016_ = v_optionFlags_3026_;
v___y_3017_ = v_isRecordingDeps_3028_;
v___y_3018_ = v_currRecDepth_3024_;
goto v___jp_3012_;
}
else
{
lean_object* v___x_3035_; 
lean_dec_ref(v_x_2995_);
lean_inc(v_ref_3025_);
v___x_3035_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_3025_);
v___y_3003_ = v___x_3035_;
goto v___jp_3002_;
}
}
else
{
lean_inc(v_ref_3025_);
v___y_3013_ = v_suppressElabErrors_3027_;
v___y_3014_ = v_ref_3025_;
v___y_3015_ = v_toCold_3023_;
v___y_3016_ = v_optionFlags_3026_;
v___y_3017_ = v_isRecordingDeps_3028_;
v___y_3018_ = v_currRecDepth_3024_;
goto v___jp_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_apply_1(v_x_3056_, lean_box(0));
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3064_, lean_object* v_x_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(v_00_u03b1_3064_, v_x_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_3072_, lean_object* v_post_3073_, size_t v_sz_3074_, size_t v_i_3075_, lean_object* v_bs_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
uint8_t v___x_3083_; 
v___x_3083_ = lean_usize_dec_lt(v_i_3075_, v_sz_3074_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; 
lean_dec_ref(v_post_3073_);
lean_dec_ref(v_pre_3072_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v_bs_3076_);
return v___x_3084_;
}
else
{
lean_object* v_v_3085_; lean_object* v___x_3086_; lean_object* v_bs_x27_3087_; lean_object* v___x_3088_; 
v_v_3085_ = lean_array_uget(v_bs_3076_, v_i_3075_);
v___x_3086_ = lean_unsigned_to_nat(0u);
v_bs_x27_3087_ = lean_array_uset(v_bs_3076_, v_i_3075_, v___x_3086_);
lean_inc_ref(v_post_3073_);
lean_inc_ref(v_pre_3072_);
v___x_3088_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3072_, v_post_3073_, v_v_3085_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3090_ = ((size_t)1ULL);
v___x_3091_ = lean_usize_add(v_i_3075_, v___x_3090_);
v___x_3092_ = lean_array_uset(v_bs_x27_3087_, v_i_3075_, v_a_3089_);
v_i_3075_ = v___x_3091_;
v_bs_3076_ = v___x_3092_;
goto _start;
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v_bs_x27_3087_);
lean_dec_ref(v_post_3073_);
lean_dec_ref(v_pre_3072_);
v_a_3094_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3088_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3088_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_3102_, lean_object* v_post_3103_, lean_object* v_x_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
if (lean_obj_tag(v_x_3104_) == 5)
{
lean_object* v_fn_3113_; lean_object* v_arg_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_fn_3113_ = lean_ctor_get(v_x_3104_, 0);
lean_inc_ref(v_fn_3113_);
v_arg_3114_ = lean_ctor_get(v_x_3104_, 1);
lean_inc_ref(v_arg_3114_);
lean_dec_ref_known(v_x_3104_, 2);
v___x_3115_ = lean_array_set(v_x_3105_, v_x_3106_, v_arg_3114_);
v___x_3116_ = lean_unsigned_to_nat(1u);
v___x_3117_ = lean_nat_sub(v_x_3106_, v___x_3116_);
lean_dec(v_x_3106_);
v_x_3104_ = v_fn_3113_;
v_x_3105_ = v___x_3115_;
v_x_3106_ = v___x_3117_;
goto _start;
}
else
{
lean_object* v___x_3119_; 
lean_dec(v_x_3106_);
lean_inc_ref(v_post_3103_);
lean_inc_ref(v_pre_3102_);
v___x_3119_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3102_, v_post_3103_, v_x_3104_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; size_t v_sz_3121_; size_t v___x_3122_; lean_object* v___x_3123_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v_sz_3121_ = lean_array_size(v_x_3105_);
v___x_3122_ = ((size_t)0ULL);
lean_inc_ref(v_post_3103_);
lean_inc_ref(v_pre_3102_);
v___x_3123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3102_, v_post_3103_, v_sz_3121_, v___x_3122_, v_x_3105_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v___x_3125_ = l_Lean_mkAppN(v_a_3120_, v_a_3124_);
lean_dec(v_a_3124_);
v___x_3126_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3102_, v_post_3103_, v___x_3125_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
return v___x_3126_;
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_a_3120_);
lean_dec_ref(v_post_3103_);
lean_dec_ref(v_pre_3102_);
v_a_3127_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3123_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3123_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_dec_ref(v_x_3105_);
lean_dec_ref(v_post_3103_);
lean_dec_ref(v_pre_3102_);
return v___x_3119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v___x_3135_, lean_object* v_pre_3136_, lean_object* v_e_3137_, lean_object* v_post_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_Core_checkSystem(v___x_3135_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v___x_3146_; 
lean_dec_ref_known(v___x_3145_, 1);
lean_inc_ref(v_pre_3136_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
lean_inc(v___y_3141_);
lean_inc_ref(v___y_3140_);
lean_inc_ref(v_e_3137_);
v___x_3146_ = lean_apply_6(v_pre_3136_, v_e_3137_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, lean_box(0));
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3262_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3262_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3262_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___y_3152_; 
switch(lean_obj_tag(v_a_3147_))
{
case 0:
{
lean_object* v_e_3252_; lean_object* v___x_3254_; 
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_e_3137_);
lean_dec_ref(v_pre_3136_);
v_e_3252_ = lean_ctor_get(v_a_3147_, 0);
lean_inc_ref(v_e_3252_);
lean_dec_ref_known(v_a_3147_, 1);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v_e_3252_);
v___x_3254_ = v___x_3149_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_e_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
case 1:
{
lean_object* v_e_3256_; lean_object* v___x_3257_; 
lean_del_object(v___x_3149_);
lean_dec_ref(v_e_3137_);
v_e_3256_ = lean_ctor_get(v_a_3147_, 0);
lean_inc_ref(v_e_3256_);
lean_dec_ref_known(v_a_3147_, 1);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3257_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_e_3256_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3257_, 1);
v___x_3259_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v_a_3258_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3259_;
}
else
{
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3257_;
}
}
default: 
{
lean_object* v_e_x3f_3260_; 
lean_del_object(v___x_3149_);
v_e_x3f_3260_ = lean_ctor_get(v_a_3147_, 0);
lean_inc(v_e_x3f_3260_);
lean_dec_ref_known(v_a_3147_, 1);
if (lean_obj_tag(v_e_x3f_3260_) == 0)
{
v___y_3152_ = v_e_3137_;
goto v___jp_3151_;
}
else
{
lean_object* v_val_3261_; 
lean_dec_ref(v_e_3137_);
v_val_3261_ = lean_ctor_get(v_e_x3f_3260_, 0);
lean_inc(v_val_3261_);
lean_dec_ref_known(v_e_x3f_3260_, 1);
v___y_3152_ = v_val_3261_;
goto v___jp_3151_;
}
}
}
v___jp_3151_:
{
switch(lean_obj_tag(v___y_3152_))
{
case 7:
{
lean_object* v_binderName_3153_; lean_object* v_binderType_3154_; lean_object* v_body_3155_; uint8_t v_binderInfo_3156_; lean_object* v___x_3157_; 
v_binderName_3153_ = lean_ctor_get(v___y_3152_, 0);
v_binderType_3154_ = lean_ctor_get(v___y_3152_, 1);
v_body_3155_ = lean_ctor_get(v___y_3152_, 2);
v_binderInfo_3156_ = lean_ctor_get_uint8(v___y_3152_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3154_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3157_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_binderType_3154_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3159_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
lean_inc_ref(v_body_3155_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3159_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_body_3155_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; size_t v___x_3161_; size_t v___x_3162_; uint8_t v___x_3163_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_ptr_addr(v_binderType_3154_);
v___x_3162_ = lean_ptr_addr(v_a_3158_);
v___x_3163_ = lean_usize_dec_eq(v___x_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_inc(v_binderName_3153_);
lean_dec_ref_known(v___y_3152_, 3);
v___x_3164_ = l_Lean_Expr_forallE___override(v_binderName_3153_, v_a_3158_, v_a_3160_, v_binderInfo_3156_);
v___x_3165_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3164_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3165_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; uint8_t v___x_3168_; 
v___x_3166_ = lean_ptr_addr(v_body_3155_);
v___x_3167_ = lean_ptr_addr(v_a_3160_);
v___x_3168_ = lean_usize_dec_eq(v___x_3166_, v___x_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_inc(v_binderName_3153_);
lean_dec_ref_known(v___y_3152_, 3);
v___x_3169_ = l_Lean_Expr_forallE___override(v_binderName_3153_, v_a_3158_, v_a_3160_, v_binderInfo_3156_);
v___x_3170_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3169_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3170_;
}
else
{
uint8_t v___x_3171_; 
v___x_3171_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3156_, v_binderInfo_3156_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_inc(v_binderName_3153_);
lean_dec_ref_known(v___y_3152_, 3);
v___x_3172_ = l_Lean_Expr_forallE___override(v_binderName_3153_, v_a_3158_, v_a_3160_, v_binderInfo_3156_);
v___x_3173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3172_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3173_;
}
else
{
lean_object* v___x_3174_; 
lean_dec(v_a_3160_);
lean_dec(v_a_3158_);
v___x_3174_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___y_3152_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3174_;
}
}
}
}
else
{
lean_dec(v_a_3158_);
lean_dec_ref_known(v___y_3152_, 3);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3159_;
}
}
else
{
lean_dec_ref_known(v___y_3152_, 3);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3157_;
}
}
case 6:
{
lean_object* v_binderName_3175_; lean_object* v_binderType_3176_; lean_object* v_body_3177_; uint8_t v_binderInfo_3178_; lean_object* v___x_3179_; 
v_binderName_3175_ = lean_ctor_get(v___y_3152_, 0);
v_binderType_3176_ = lean_ctor_get(v___y_3152_, 1);
v_body_3177_ = lean_ctor_get(v___y_3152_, 2);
v_binderInfo_3178_ = lean_ctor_get_uint8(v___y_3152_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3176_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_binderType_3176_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3181_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
lean_inc_ref(v_body_3177_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3181_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_body_3177_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; size_t v___x_3183_; size_t v___x_3184_; uint8_t v___x_3185_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = lean_ptr_addr(v_binderType_3176_);
v___x_3184_ = lean_ptr_addr(v_a_3180_);
v___x_3185_ = lean_usize_dec_eq(v___x_3183_, v___x_3184_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc(v_binderName_3175_);
lean_dec_ref_known(v___y_3152_, 3);
v___x_3186_ = l_Lean_Expr_lam___override(v_binderName_3175_, v_a_3180_, v_a_3182_, v_binderInfo_3178_);
v___x_3187_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3186_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3187_;
}
else
{
size_t v___x_3188_; size_t v___x_3189_; uint8_t v___x_3190_; 
v___x_3188_ = lean_ptr_addr(v_body_3177_);
v___x_3189_ = lean_ptr_addr(v_a_3182_);
v___x_3190_ = lean_usize_dec_eq(v___x_3188_, v___x_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_inc(v_binderName_3175_);
lean_dec_ref_known(v___y_3152_, 3);
v___x_3191_ = l_Lean_Expr_lam___override(v_binderName_3175_, v_a_3180_, v_a_3182_, v_binderInfo_3178_);
v___x_3192_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3191_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3192_;
}
else
{
uint8_t v___x_3193_; 
v___x_3193_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3178_, v_binderInfo_3178_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_inc(v_binderName_3175_);
lean_dec_ref_known(v___y_3152_, 3);
v___x_3194_ = l_Lean_Expr_lam___override(v_binderName_3175_, v_a_3180_, v_a_3182_, v_binderInfo_3178_);
v___x_3195_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3194_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; 
lean_dec(v_a_3182_);
lean_dec(v_a_3180_);
v___x_3196_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___y_3152_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3196_;
}
}
}
}
else
{
lean_dec(v_a_3180_);
lean_dec_ref_known(v___y_3152_, 3);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3181_;
}
}
else
{
lean_dec_ref_known(v___y_3152_, 3);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3179_;
}
}
case 8:
{
lean_object* v_declName_3197_; lean_object* v_type_3198_; lean_object* v_value_3199_; lean_object* v_body_3200_; uint8_t v_nondep_3201_; lean_object* v___x_3202_; 
v_declName_3197_ = lean_ctor_get(v___y_3152_, 0);
v_type_3198_ = lean_ctor_get(v___y_3152_, 1);
v_value_3199_ = lean_ctor_get(v___y_3152_, 2);
v_body_3200_ = lean_ctor_get(v___y_3152_, 3);
v_nondep_3201_ = lean_ctor_get_uint8(v___y_3152_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3198_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3202_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_type_3198_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3204_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 1);
lean_inc_ref(v_value_3199_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3204_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_value_3199_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
lean_inc_ref(v_body_3200_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3206_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_body_3200_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; size_t v___x_3208_; size_t v___x_3209_; uint8_t v___x_3210_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___x_3206_, 1);
v___x_3208_ = lean_ptr_addr(v_type_3198_);
v___x_3209_ = lean_ptr_addr(v_a_3203_);
v___x_3210_ = lean_usize_dec_eq(v___x_3208_, v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_inc(v_declName_3197_);
lean_dec_ref_known(v___y_3152_, 4);
v___x_3211_ = l_Lean_Expr_letE___override(v_declName_3197_, v_a_3203_, v_a_3205_, v_a_3207_, v_nondep_3201_);
v___x_3212_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3211_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3212_;
}
else
{
size_t v___x_3213_; size_t v___x_3214_; uint8_t v___x_3215_; 
v___x_3213_ = lean_ptr_addr(v_value_3199_);
v___x_3214_ = lean_ptr_addr(v_a_3205_);
v___x_3215_ = lean_usize_dec_eq(v___x_3213_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_inc(v_declName_3197_);
lean_dec_ref_known(v___y_3152_, 4);
v___x_3216_ = l_Lean_Expr_letE___override(v_declName_3197_, v_a_3203_, v_a_3205_, v_a_3207_, v_nondep_3201_);
v___x_3217_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3216_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3217_;
}
else
{
size_t v___x_3218_; size_t v___x_3219_; uint8_t v___x_3220_; 
v___x_3218_ = lean_ptr_addr(v_body_3200_);
v___x_3219_ = lean_ptr_addr(v_a_3207_);
v___x_3220_ = lean_usize_dec_eq(v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc(v_declName_3197_);
lean_dec_ref_known(v___y_3152_, 4);
v___x_3221_ = l_Lean_Expr_letE___override(v_declName_3197_, v_a_3203_, v_a_3205_, v_a_3207_, v_nondep_3201_);
v___x_3222_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3221_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; 
lean_dec(v_a_3207_);
lean_dec(v_a_3205_);
lean_dec(v_a_3203_);
v___x_3223_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___y_3152_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3223_;
}
}
}
}
else
{
lean_dec(v_a_3205_);
lean_dec(v_a_3203_);
lean_dec_ref_known(v___y_3152_, 4);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3206_;
}
}
else
{
lean_dec(v_a_3203_);
lean_dec_ref_known(v___y_3152_, 4);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3204_;
}
}
else
{
lean_dec_ref_known(v___y_3152_, 4);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3202_;
}
}
case 5:
{
lean_object* v_dummy_3224_; lean_object* v_nargs_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_dummy_3224_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3225_ = l_Lean_Expr_getAppNumArgs(v___y_3152_);
lean_inc(v_nargs_3225_);
v___x_3226_ = lean_mk_array(v_nargs_3225_, v_dummy_3224_);
v___x_3227_ = lean_unsigned_to_nat(1u);
v___x_3228_ = lean_nat_sub(v_nargs_3225_, v___x_3227_);
lean_dec(v_nargs_3225_);
v___x_3229_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3136_, v_post_3138_, v___y_3152_, v___x_3226_, v___x_3228_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3229_;
}
case 10:
{
lean_object* v_data_3230_; lean_object* v_expr_3231_; lean_object* v___x_3232_; 
v_data_3230_ = lean_ctor_get(v___y_3152_, 0);
v_expr_3231_ = lean_ctor_get(v___y_3152_, 1);
lean_inc_ref(v_expr_3231_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3232_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_expr_3231_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; size_t v___x_3234_; size_t v___x_3235_; uint8_t v___x_3236_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = lean_ptr_addr(v_expr_3231_);
v___x_3235_ = lean_ptr_addr(v_a_3233_);
v___x_3236_ = lean_usize_dec_eq(v___x_3234_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_inc(v_data_3230_);
lean_dec_ref_known(v___y_3152_, 2);
v___x_3237_ = l_Lean_Expr_mdata___override(v_data_3230_, v_a_3233_);
v___x_3238_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3237_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3238_;
}
else
{
lean_object* v___x_3239_; 
lean_dec(v_a_3233_);
v___x_3239_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___y_3152_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3239_;
}
}
else
{
lean_dec_ref_known(v___y_3152_, 2);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3232_;
}
}
case 11:
{
lean_object* v_typeName_3240_; lean_object* v_idx_3241_; lean_object* v_struct_3242_; lean_object* v___x_3243_; 
v_typeName_3240_ = lean_ctor_get(v___y_3152_, 0);
v_idx_3241_ = lean_ctor_get(v___y_3152_, 1);
v_struct_3242_ = lean_ctor_get(v___y_3152_, 2);
lean_inc_ref(v_struct_3242_);
lean_inc_ref(v_post_3138_);
lean_inc_ref(v_pre_3136_);
v___x_3243_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3136_, v_post_3138_, v_struct_3242_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; size_t v___x_3245_; size_t v___x_3246_; uint8_t v___x_3247_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
v___x_3245_ = lean_ptr_addr(v_struct_3242_);
v___x_3246_ = lean_ptr_addr(v_a_3244_);
v___x_3247_ = lean_usize_dec_eq(v___x_3245_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_inc(v_idx_3241_);
lean_inc(v_typeName_3240_);
lean_dec_ref_known(v___y_3152_, 3);
v___x_3248_ = l_Lean_Expr_proj___override(v_typeName_3240_, v_idx_3241_, v_a_3244_);
v___x_3249_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___x_3248_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; 
lean_dec(v_a_3244_);
v___x_3250_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___y_3152_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3250_;
}
}
else
{
lean_dec_ref_known(v___y_3152_, 3);
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_pre_3136_);
return v___x_3243_;
}
}
default: 
{
lean_object* v___x_3251_; 
v___x_3251_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3136_, v_post_3138_, v___y_3152_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3251_;
}
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_e_3137_);
lean_dec_ref(v_pre_3136_);
v_a_3263_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3146_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3146_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v_post_3138_);
lean_dec_ref(v_e_3137_);
lean_dec_ref(v_pre_3136_);
v_a_3271_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3145_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3145_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v___x_3279_, lean_object* v_pre_3280_, lean_object* v_e_3281_, lean_object* v_post_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_3279_, v_pre_3280_, v_e_3281_, v_post_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_3290_, lean_object* v_post_3291_, lean_object* v_e_3292_, lean_object* v_a_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_inc(v_a_3293_);
v___x_3299_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3299_, 0, lean_box(0));
lean_closure_set(v___x_3299_, 1, lean_box(0));
lean_closure_set(v___x_3299_, 2, v_a_3293_);
v___x_3300_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___x_3299_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3332_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3332_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3332_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3301_, v_e_3292_);
lean_dec(v_a_3301_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v___x_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; 
lean_del_object(v___x_3303_);
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_3292_);
v___f_3307_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3307_, 0, v___x_3306_);
lean_closure_set(v___f_3307_, 1, v_pre_3290_);
lean_closure_set(v___f_3307_, 2, v_e_3292_);
lean_closure_set(v___f_3307_, 3, v_post_3291_);
v___x_3308_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_3307_, v_a_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___f_3310_; lean_object* v___x_3311_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc_n(v_a_3309_, 2);
lean_dec_ref_known(v___x_3308_, 1);
lean_inc(v_a_3293_);
v___f_3310_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3310_, 0, v_a_3293_);
lean_closure_set(v___f_3310_, 1, v_e_3292_);
lean_closure_set(v___f_3310_, 2, v_a_3309_);
v___x_3311_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(lean_box(0), v___f_3310_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; 
v_unused_3319_ = lean_ctor_get(v___x_3311_, 0);
lean_dec(v_unused_3319_);
v___x_3313_ = v___x_3311_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_dec(v___x_3311_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v_a_3309_);
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3309_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_a_3309_);
v_a_3320_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3311_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3311_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
lean_dec_ref(v_e_3292_);
return v___x_3308_;
}
}
else
{
lean_object* v_val_3328_; lean_object* v___x_3330_; 
lean_dec_ref(v_e_3292_);
lean_dec_ref(v_post_3291_);
lean_dec_ref(v_pre_3290_);
v_val_3328_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v___x_3305_, 1);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v_val_3328_);
v___x_3330_ = v___x_3303_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_val_3328_);
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
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref(v_e_3292_);
lean_dec_ref(v_post_3291_);
lean_dec_ref(v_pre_3290_);
v_a_3333_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3300_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3300_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_3341_, lean_object* v_post_3342_, lean_object* v_e_3343_, lean_object* v_a_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
lean_inc_ref(v_post_3342_);
lean_inc(v___y_3348_);
lean_inc_ref(v___y_3347_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc_ref(v_e_3343_);
v___x_3350_ = lean_apply_6(v_post_3342_, v_e_3343_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, lean_box(0));
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3369_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3369_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3369_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
switch(lean_obj_tag(v_a_3351_))
{
case 0:
{
lean_object* v_e_3355_; lean_object* v___x_3357_; 
lean_dec_ref(v_e_3343_);
lean_dec_ref(v_post_3342_);
lean_dec_ref(v_pre_3341_);
v_e_3355_ = lean_ctor_get(v_a_3351_, 0);
lean_inc_ref(v_e_3355_);
lean_dec_ref_known(v_a_3351_, 1);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v_e_3355_);
v___x_3357_ = v___x_3353_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_e_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
case 1:
{
lean_object* v_e_3359_; lean_object* v___x_3360_; 
lean_del_object(v___x_3353_);
lean_dec_ref(v_e_3343_);
v_e_3359_ = lean_ctor_get(v_a_3351_, 0);
lean_inc_ref(v_e_3359_);
lean_dec_ref_known(v_a_3351_, 1);
v___x_3360_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3341_, v_post_3342_, v_e_3359_, v_a_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3360_;
}
default: 
{
lean_object* v_e_x3f_3361_; 
lean_dec_ref(v_post_3342_);
lean_dec_ref(v_pre_3341_);
v_e_x3f_3361_ = lean_ctor_get(v_a_3351_, 0);
lean_inc(v_e_x3f_3361_);
lean_dec_ref_known(v_a_3351_, 1);
if (lean_obj_tag(v_e_x3f_3361_) == 0)
{
lean_object* v___x_3363_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v_e_3343_);
v___x_3363_ = v___x_3353_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_e_3343_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
else
{
lean_object* v_val_3365_; lean_object* v___x_3367_; 
lean_dec_ref(v_e_3343_);
v_val_3365_ = lean_ctor_get(v_e_x3f_3361_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v_e_x3f_3361_, 1);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v_val_3365_);
v___x_3367_ = v___x_3353_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_val_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec_ref(v_e_3343_);
lean_dec_ref(v_post_3342_);
lean_dec_ref(v_pre_3341_);
v_a_3370_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3350_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3350_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_3378_, lean_object* v_post_3379_, lean_object* v_e_3380_, lean_object* v_a_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_3378_, v_post_3379_, v_e_3380_, v_a_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v_a_3381_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_3388_, lean_object* v_post_3389_, lean_object* v_sz_3390_, lean_object* v_i_3391_, lean_object* v_bs_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
size_t v_sz_boxed_3399_; size_t v_i_boxed_3400_; lean_object* v_res_3401_; 
v_sz_boxed_3399_ = lean_unbox_usize(v_sz_3390_);
lean_dec(v_sz_3390_);
v_i_boxed_3400_ = lean_unbox_usize(v_i_3391_);
lean_dec(v_i_3391_);
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_3388_, v_post_3389_, v_sz_boxed_3399_, v_i_boxed_3400_, v_bs_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_3402_, lean_object* v_post_3403_, lean_object* v_x_3404_, lean_object* v_x_3405_, lean_object* v_x_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_3402_, v_post_3403_, v_x_3404_, v_x_3405_, v_x_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_3414_, lean_object* v_post_3415_, lean_object* v_e_3416_, lean_object* v_a_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3414_, v_post_3415_, v_e_3416_, v_a_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v_a_3417_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_3424_, lean_object* v_pre_3425_, lean_object* v_post_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v_a_3434_; lean_object* v___x_3435_; 
v___x_3432_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_3433_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3432_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref(v___x_3433_);
v___x_3435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_3425_, v_post_3426_, v_input_3424_, v_a_3434_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3435_, 1);
v___x_3437_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3437_, 0, lean_box(0));
lean_closure_set(v___x_3437_, 1, lean_box(0));
lean_closure_set(v___x_3437_, 2, v_a_3434_);
v___x_3438_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(lean_box(0), v___x_3437_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___x_3438_, 0);
lean_dec(v_unused_3446_);
v___x_3440_ = v___x_3438_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_dec(v___x_3438_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_a_3436_);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3436_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_dec(v_a_3434_);
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_3447_, lean_object* v_pre_3448_, lean_object* v_post_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_3447_, v_pre_3448_, v_post_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_3466_ = lean_find_expr(v___x_3465_, v_e_3459_);
if (lean_obj_tag(v___x_3466_) == 0)
{
uint8_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = 1;
v___x_3468_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3468_, 0, v_e_3459_);
lean_ctor_set(v___x_3468_, 1, v___x_3466_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*2, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
else
{
lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3518_; 
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3518_ == 0)
{
lean_object* v_unused_3519_; 
v_unused_3519_ = lean_ctor_get(v___x_3466_, 0);
lean_dec(v_unused_3519_);
v___x_3471_ = v___x_3466_;
v_isShared_3472_ = v_isSharedCheck_3518_;
goto v_resetjp_3470_;
}
else
{
lean_dec(v___x_3466_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3518_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v_pre_3473_; lean_object* v___f_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; 
v_pre_3473_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_3474_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
v___x_3475_ = 1;
lean_inc_ref(v_e_3459_);
v___x_3476_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_3459_, v_pre_3473_, v___f_3474_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3478_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc_n(v_a_3477_, 2);
lean_dec_ref_known(v___x_3476_, 1);
v___x_3478_ = l_Lean_Meta_mkEqRefl(v_a_3477_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3480_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
lean_inc(v_a_3477_);
v___x_3480_ = l_Lean_Meta_mkEq(v_e_3459_, v_a_3477_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3493_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3493_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3493_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3485_ = l_Lean_Meta_mkExpectedPropHint(v_a_3479_, v_a_3481_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3485_);
v___x_3487_ = v___x_3471_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3488_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3488_, 0, v_a_3477_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
lean_ctor_set_uint8(v___x_3488_, sizeof(void*)*2, v___x_3475_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3488_);
v___x_3490_ = v___x_3483_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_a_3479_);
lean_dec(v_a_3477_);
lean_del_object(v___x_3471_);
v_a_3494_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3480_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3480_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_a_3477_);
lean_del_object(v___x_3471_);
lean_dec_ref(v_e_3459_);
v_a_3502_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3478_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3478_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_del_object(v___x_3471_);
lean_dec_ref(v_e_3459_);
v_a_3510_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3476_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3476_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3527_, lean_object* v_x_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3536_, lean_object* v_x_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_3536_, v_x_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
return v_res_3544_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_3548_){
_start:
{
lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3549_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_3550_ = l_Lean_Expr_isAppOf(v_e_3548_, v___x_3549_);
if (v___x_3550_ == 0)
{
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3551_ = lean_unsigned_to_nat(5u);
v___x_3552_ = l_Lean_Expr_getAppNumArgs(v_e_3548_);
v___x_3553_ = lean_nat_dec_le(v___x_3551_, v___x_3552_);
lean_dec(v___x_3552_);
return v___x_3553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_3554_){
_start:
{
uint8_t v_res_3555_; lean_object* v_r_3556_; 
v_res_3555_ = l_Lean_Meta_Grind_isIte(v_e_3554_);
lean_dec_ref(v_e_3554_);
v_r_3556_ = lean_box(v_res_3555_);
return v_r_3556_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_3560_){
_start:
{
lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3561_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_3562_ = l_Lean_Expr_isAppOf(v_e_3560_, v___x_3561_);
if (v___x_3562_ == 0)
{
return v___x_3562_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3563_ = lean_unsigned_to_nat(5u);
v___x_3564_ = l_Lean_Expr_getAppNumArgs(v_e_3560_);
v___x_3565_ = lean_nat_dec_le(v___x_3563_, v___x_3564_);
lean_dec(v___x_3564_);
return v___x_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_3566_){
_start:
{
uint8_t v_res_3567_; lean_object* v_r_3568_; 
v_res_3567_ = l_Lean_Meta_Grind_isDIte(v_e_3566_);
lean_dec_ref(v_e_3566_);
v_r_3568_ = lean_box(v_res_3567_);
return v_r_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_3569_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = l_Lean_Expr_isApp(v_e_3569_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_box(0);
return v___x_3571_;
}
else
{
lean_object* v_f_3572_; uint8_t v___x_3573_; 
v_f_3572_ = l_Lean_Expr_appFn_x21(v_e_3569_);
v___x_3573_ = l_Lean_Expr_isApp(v_f_3572_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; 
lean_dec_ref(v_f_3572_);
v___x_3574_ = lean_box(0);
return v___x_3574_;
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = l_Lean_Expr_appFn_x21(v_f_3572_);
lean_dec_ref(v_f_3572_);
v___x_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
return v___x_3576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Meta_Grind_getBinOp(v_e_3577_);
lean_dec_ref(v_e_3577_);
return v_res_3578_;
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
res = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__53_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_11_();
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
