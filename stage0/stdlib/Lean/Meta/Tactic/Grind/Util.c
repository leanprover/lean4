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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedLocalContext_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "issues"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_ensureNoMVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 26, 246, 148, 197, 20, 141, 244)}};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "found `Expr.proj` with invalid field index `"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_foldProjs___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_foldProjs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isProj___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_foldProjs___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_foldProjs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_foldProjs___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_foldProjs___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_foldProjs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_foldProjs___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_foldProjs___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
lean_dec_ref(v___x_60_);
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
v___x_91_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_toApplicative_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_165_; 
v___x_102_ = lean_obj_once(&l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0, &l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0);
v___x_103_ = l_ReaderT_instMonad___redArg(v___x_102_);
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
v___x_127_ = l_ReaderT_instMonad___redArg(v___x_126_);
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
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_1392__overap_153_; lean_object* v___x_154_; 
v___x_151_ = l_Lean_instInhabitedLocalContext_default;
v___x_152_ = l_instInhabitedOfMonad___redArg(v___x_150_, v___x_151_);
v___x_1392__overap_153_ = lean_panic_fn(v___x_152_, v_msg_96_);
v___x_154_ = lean_apply_5(v___x_1392__overap_153_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, lean_box(0));
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
lean_dec_ref(v___x_214_);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_auxDeclToFullName_192_, v_fvarId_211_);
if (lean_obj_tag(v___x_216_) == 1)
{
lean_object* v_val_217_; lean_object* v___x_218_; 
v_val_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_217_);
lean_dec_ref(v___x_216_);
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
v___x_221_ = lean_unsigned_to_nat(633u);
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
lean_inc(v___y_200_);
lean_inc_ref(v___y_199_);
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
v___x_230_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v___x_229_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v_a_203_ = v_a_231_;
goto v___jp_202_;
}
else
{
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v___x_230_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
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
lean_dec_ref(v___x_244_);
lean_inc(v_userName_241_);
lean_inc(v_fvarId_240_);
v___x_246_ = l_Lean_LocalContext_mkLocalDecl(v_b_196_, v_fvarId_240_, v_userName_241_, v_a_245_, v_bi_243_, v_kind_210_);
v_a_203_ = v___x_246_;
goto v___jp_202_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
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
lean_dec_ref(v___x_261_);
lean_inc_ref(v_value_258_);
v___x_263_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_value_258_, v___y_198_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref(v___x_263_);
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
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
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
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
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
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
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
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
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
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
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
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
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
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
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
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
lean_inc(v___x_357_);
v___x_358_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_346_, v___x_357_, v_b_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; size_t v___x_360_; size_t v___x_361_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref(v___x_358_);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_348_, v___x_360_);
v_i_348_ = v___x_361_;
v_b_350_ = v_a_359_;
goto _start;
}
else
{
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v___x_358_;
}
}
else
{
lean_object* v___x_363_; 
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
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
lean_dec_ref(v_x_388_);
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
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc(v___y_393_);
lean_inc_ref(v___y_392_);
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
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
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
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v___x_408_;
}
else
{
size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; 
lean_dec_ref(v___x_408_);
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
lean_dec_ref(v___x_408_);
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
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
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
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
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
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
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
size_t v_x_4541__boxed_452_; size_t v_x_4542__boxed_453_; lean_object* v_res_454_; 
v_x_4541__boxed_452_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_x_4542__boxed_453_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_res_454_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_442_, v_x_443_, v_x_4541__boxed_452_, v_x_4542__boxed_453_, v_x_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
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
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_460_);
lean_inc_ref(v___y_459_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v___x_472_;
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v___x_472_);
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
lean_dec_ref(v___x_472_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
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
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_460_);
lean_inc_ref(v___y_459_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v___x_497_;
}
else
{
size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v___x_497_);
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
lean_dec_ref(v___x_497_);
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
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; 
v___x_607_ = ((size_t)5ULL);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_shift_left(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; 
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0);
v___x_612_ = lean_usize_sub(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(lean_object* v_x_614_, size_t v_x_615_, size_t v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v_es_619_; size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v_j_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_es_619_ = lean_ctor_get(v_x_614_, 0);
v___x_620_ = ((size_t)5ULL);
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1);
v___x_623_ = lean_usize_land(v_x_615_, v___x_622_);
v_j_624_ = lean_usize_to_nat(v___x_623_);
v___x_625_ = lean_array_get_size(v_es_619_);
v___x_626_ = lean_nat_dec_lt(v_j_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec(v_j_624_);
lean_dec(v_x_618_);
lean_dec(v_x_617_);
return v_x_614_;
}
else
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_663_; 
lean_inc_ref(v_es_619_);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_614_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_x_614_, 0);
lean_dec(v_unused_664_);
v___x_628_ = v_x_614_;
v_isShared_629_ = v_isSharedCheck_663_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_x_614_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_663_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_v_630_; lean_object* v___x_631_; lean_object* v_xs_x27_632_; lean_object* v___y_634_; 
v_v_630_ = lean_array_fget(v_es_619_, v_j_624_);
v___x_631_ = lean_box(0);
v_xs_x27_632_ = lean_array_fset(v_es_619_, v_j_624_, v___x_631_);
switch(lean_obj_tag(v_v_630_))
{
case 0:
{
lean_object* v_key_639_; lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_650_; 
v_key_639_ = lean_ctor_get(v_v_630_, 0);
v_val_640_ = lean_ctor_get(v_v_630_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_v_630_);
if (v_isSharedCheck_650_ == 0)
{
v___x_642_ = v_v_630_;
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_inc(v_key_639_);
lean_dec(v_v_630_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
uint8_t v___x_644_; 
v___x_644_ = l_Lean_instBEqMVarId_beq(v_x_617_, v_key_639_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_del_object(v___x_642_);
v___x_645_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_639_, v_val_640_, v_x_617_, v_x_618_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___y_634_ = v___x_646_;
goto v___jp_633_;
}
else
{
lean_object* v___x_648_; 
lean_dec(v_val_640_);
lean_dec(v_key_639_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_x_618_);
lean_ctor_set(v___x_642_, 0, v_x_617_);
v___x_648_ = v___x_642_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_x_617_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_x_618_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
v___y_634_ = v___x_648_;
goto v___jp_633_;
}
}
}
}
case 1:
{
lean_object* v_node_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_661_; 
v_node_651_ = lean_ctor_get(v_v_630_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_v_630_);
if (v_isSharedCheck_661_ == 0)
{
v___x_653_ = v_v_630_;
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_node_651_);
lean_dec(v_v_630_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_655_ = lean_usize_shift_right(v_x_615_, v___x_620_);
v___x_656_ = lean_usize_add(v_x_616_, v___x_621_);
v___x_657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_node_651_, v___x_655_, v___x_656_, v_x_617_, v_x_618_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_657_);
v___x_659_ = v___x_653_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
v___y_634_ = v___x_659_;
goto v___jp_633_;
}
}
}
default: 
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_x_617_);
lean_ctor_set(v___x_662_, 1, v_x_618_);
v___y_634_ = v___x_662_;
goto v___jp_633_;
}
}
v___jp_633_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_array_fset(v_xs_x27_632_, v_j_624_, v___y_634_);
lean_dec(v_j_624_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_635_);
v___x_637_ = v___x_628_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
else
{
lean_object* v_ks_665_; lean_object* v_vs_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_686_; 
v_ks_665_ = lean_ctor_get(v_x_614_, 0);
v_vs_666_ = lean_ctor_get(v_x_614_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_614_);
if (v_isSharedCheck_686_ == 0)
{
v___x_668_ = v_x_614_;
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_vs_666_);
lean_inc(v_ks_665_);
lean_dec(v_x_614_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_ks_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_vs_666_);
v___x_671_ = v_reuseFailAlloc_685_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v_newNode_672_; uint8_t v___y_674_; size_t v___x_680_; uint8_t v___x_681_; 
v_newNode_672_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v___x_671_, v_x_617_, v_x_618_);
v___x_680_ = ((size_t)7ULL);
v___x_681_ = lean_usize_dec_le(v___x_680_, v_x_616_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_672_);
v___x_683_ = lean_unsigned_to_nat(4u);
v___x_684_ = lean_nat_dec_lt(v___x_682_, v___x_683_);
lean_dec(v___x_682_);
v___y_674_ = v___x_684_;
goto v___jp_673_;
}
else
{
v___y_674_ = v___x_681_;
goto v___jp_673_;
}
v___jp_673_:
{
if (v___y_674_ == 0)
{
lean_object* v_ks_675_; lean_object* v_vs_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_ks_675_ = lean_ctor_get(v_newNode_672_, 0);
lean_inc_ref(v_ks_675_);
v_vs_676_ = lean_ctor_get(v_newNode_672_, 1);
lean_inc_ref(v_vs_676_);
lean_dec_ref(v_newNode_672_);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2);
v___x_679_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_x_616_, v_ks_675_, v_vs_676_, v___x_677_, v___x_678_);
lean_dec_ref(v_vs_676_);
lean_dec_ref(v_ks_675_);
return v___x_679_;
}
else
{
return v_newNode_672_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(size_t v_depth_687_, lean_object* v_keys_688_, lean_object* v_vals_689_, lean_object* v_i_690_, lean_object* v_entries_691_){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_array_get_size(v_keys_688_);
v___x_693_ = lean_nat_dec_lt(v_i_690_, v___x_692_);
if (v___x_693_ == 0)
{
lean_dec(v_i_690_);
return v_entries_691_;
}
else
{
lean_object* v_k_694_; lean_object* v_v_695_; uint64_t v___x_696_; size_t v_h_697_; size_t v___x_698_; lean_object* v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v_h_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_k_694_ = lean_array_fget_borrowed(v_keys_688_, v_i_690_);
v_v_695_ = lean_array_fget_borrowed(v_vals_689_, v_i_690_);
v___x_696_ = l_Lean_instHashableMVarId_hash(v_k_694_);
v_h_697_ = lean_uint64_to_usize(v___x_696_);
v___x_698_ = ((size_t)5ULL);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_sub(v_depth_687_, v___x_700_);
v___x_702_ = lean_usize_mul(v___x_698_, v___x_701_);
v_h_703_ = lean_usize_shift_right(v_h_697_, v___x_702_);
v___x_704_ = lean_nat_add(v_i_690_, v___x_699_);
lean_dec(v_i_690_);
lean_inc(v_v_695_);
lean_inc(v_k_694_);
v___x_705_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_entries_691_, v_h_703_, v_depth_687_, v_k_694_, v_v_695_);
v_i_690_ = v___x_704_;
v_entries_691_ = v___x_705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg___boxed(lean_object* v_depth_707_, lean_object* v_keys_708_, lean_object* v_vals_709_, lean_object* v_i_710_, lean_object* v_entries_711_){
_start:
{
size_t v_depth_boxed_712_; lean_object* v_res_713_; 
v_depth_boxed_712_ = lean_unbox_usize(v_depth_707_);
lean_dec(v_depth_707_);
v_res_713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_boxed_712_, v_keys_708_, v_vals_709_, v_i_710_, v_entries_711_);
lean_dec_ref(v_vals_709_);
lean_dec_ref(v_keys_708_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
size_t v_x_4927__boxed_719_; size_t v_x_4928__boxed_720_; lean_object* v_res_721_; 
v_x_4927__boxed_719_ = lean_unbox_usize(v_x_715_);
lean_dec(v_x_715_);
v_x_4928__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_714_, v_x_4927__boxed_719_, v_x_4928__boxed_720_, v_x_717_, v_x_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
uint64_t v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_725_ = l_Lean_instHashableMVarId_hash(v_x_723_);
v___x_726_ = lean_uint64_to_usize(v___x_725_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_722_, v___x_726_, v___x_727_, v_x_723_, v_x_724_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(lean_object* v_mvarId_729_, lean_object* v_val_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; lean_object* v_mctx_734_; lean_object* v_cache_735_; lean_object* v_zetaDeltaFVarIds_736_; lean_object* v_postponed_737_; lean_object* v_diag_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_765_; 
v___x_733_ = lean_st_ref_take(v___y_731_);
v_mctx_734_ = lean_ctor_get(v___x_733_, 0);
v_cache_735_ = lean_ctor_get(v___x_733_, 1);
v_zetaDeltaFVarIds_736_ = lean_ctor_get(v___x_733_, 2);
v_postponed_737_ = lean_ctor_get(v___x_733_, 3);
v_diag_738_ = lean_ctor_get(v___x_733_, 4);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_765_ == 0)
{
v___x_740_ = v___x_733_;
v_isShared_741_ = v_isSharedCheck_765_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_diag_738_);
lean_inc(v_postponed_737_);
lean_inc(v_zetaDeltaFVarIds_736_);
lean_inc(v_cache_735_);
lean_inc(v_mctx_734_);
lean_dec(v___x_733_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_765_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_depth_742_; lean_object* v_levelAssignDepth_743_; lean_object* v_mvarCounter_744_; lean_object* v_lDepth_745_; lean_object* v_decls_746_; lean_object* v_userNames_747_; lean_object* v_lAssignment_748_; lean_object* v_eAssignment_749_; lean_object* v_dAssignment_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_764_; 
v_depth_742_ = lean_ctor_get(v_mctx_734_, 0);
v_levelAssignDepth_743_ = lean_ctor_get(v_mctx_734_, 1);
v_mvarCounter_744_ = lean_ctor_get(v_mctx_734_, 2);
v_lDepth_745_ = lean_ctor_get(v_mctx_734_, 3);
v_decls_746_ = lean_ctor_get(v_mctx_734_, 4);
v_userNames_747_ = lean_ctor_get(v_mctx_734_, 5);
v_lAssignment_748_ = lean_ctor_get(v_mctx_734_, 6);
v_eAssignment_749_ = lean_ctor_get(v_mctx_734_, 7);
v_dAssignment_750_ = lean_ctor_get(v_mctx_734_, 8);
v_isSharedCheck_764_ = !lean_is_exclusive(v_mctx_734_);
if (v_isSharedCheck_764_ == 0)
{
v___x_752_ = v_mctx_734_;
v_isShared_753_ = v_isSharedCheck_764_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_dAssignment_750_);
lean_inc(v_eAssignment_749_);
lean_inc(v_lAssignment_748_);
lean_inc(v_userNames_747_);
lean_inc(v_decls_746_);
lean_inc(v_lDepth_745_);
lean_inc(v_mvarCounter_744_);
lean_inc(v_levelAssignDepth_743_);
lean_inc(v_depth_742_);
lean_dec(v_mctx_734_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_764_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_749_, v_mvarId_729_, v_val_730_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 7, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_depth_742_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_levelAssignDepth_743_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_mvarCounter_744_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_lDepth_745_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_decls_746_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v_userNames_747_);
lean_ctor_set(v_reuseFailAlloc_763_, 6, v_lAssignment_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 7, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_763_, 8, v_dAssignment_750_);
v___x_756_ = v_reuseFailAlloc_763_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_756_);
v___x_758_ = v___x_740_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_cache_735_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_zetaDeltaFVarIds_736_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_postponed_737_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_diag_738_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_st_ref_set(v___y_731_, v___x_758_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(lean_object* v_mvarId_766_, lean_object* v_val_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_766_, v_val_767_, v___y_768_);
lean_dec(v___y_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars(lean_object* v_mvarId_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_771_);
v___x_778_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_771_, v___x_777_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_779_; 
lean_dec_ref(v___x_778_);
lean_inc(v_mvarId_771_);
v___x_779_ = l_Lean_MVarId_getDecl(v_mvarId_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v_userName_781_; lean_object* v_lctx_782_; lean_object* v_type_783_; lean_object* v_localInstances_784_; lean_object* v___x_785_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
v_userName_781_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_userName_781_);
v_lctx_782_ = lean_ctor_get(v_a_780_, 1);
lean_inc_ref(v_lctx_782_);
v_type_783_ = lean_ctor_get(v_a_780_, 2);
lean_inc_ref(v_type_783_);
v_localInstances_784_ = lean_ctor_get(v_a_780_, 4);
lean_inc_ref(v_localInstances_784_);
lean_dec(v_a_780_);
lean_inc(v_a_775_);
lean_inc_ref(v_a_774_);
lean_inc(v_a_773_);
lean_inc_ref(v_a_772_);
v___x_785_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_782_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; lean_object* v_a_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref(v___x_785_);
v___x_787_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_783_, v_a_773_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref(v___x_787_);
v___x_789_ = 2;
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_786_, v_localInstances_784_, v_a_788_, v___x_789_, v_userName_781_, v___x_790_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec_ref(v_a_772_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
lean_inc(v_a_792_);
v___x_793_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_771_, v_a_792_, v_a_773_);
lean_dec(v_a_773_);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v___x_793_, 0);
lean_dec(v_unused_802_);
v___x_795_ = v___x_793_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_dec(v___x_793_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = l_Lean_Expr_mvarId_x21(v_a_792_);
lean_dec(v_a_792_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_a_773_);
lean_dec(v_mvarId_771_);
v_a_803_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_791_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_791_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_localInstances_784_);
lean_dec_ref(v_type_783_);
lean_dec(v_userName_781_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_mvarId_771_);
v_a_811_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_785_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_785_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_mvarId_771_);
v_a_819_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_779_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_779_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_mvarId_771_);
v_a_827_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_778_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_778_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars___boxed(lean_object* v_mvarId_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_MVarId_instantiateGoalMVars(v_mvarId_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(lean_object* v_mvarId_842_, lean_object* v_val_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_842_, v_val_843_, v___y_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(lean_object* v_mvarId_850_, lean_object* v_val_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(v_mvarId_850_, v_val_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(lean_object* v_00_u03b4_858_, lean_object* v_t_859_, lean_object* v_k_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_859_, v_k_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b4_862_, lean_object* v_t_863_, lean_object* v_k_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(v_00_u03b4_862_, v_t_863_, v_k_864_);
lean_dec(v_k_864_);
lean_dec(v_t_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, size_t v_x_873_, size_t v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_872_, v_x_873_, v_x_874_, v_x_875_, v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_5305__boxed_884_; size_t v_x_5306__boxed_885_; lean_object* v_res_886_; 
v_x_5305__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_x_5306__boxed_885_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_res_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_878_, v_x_879_, v_x_5305__boxed_884_, v_x_5306__boxed_885_, v_x_882_, v_x_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_887_, lean_object* v_n_888_, lean_object* v_k_889_, lean_object* v_v_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v_n_888_, v_k_889_, v_v_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_892_, size_t v_depth_893_, lean_object* v_keys_894_, lean_object* v_vals_895_, lean_object* v_heq_896_, lean_object* v_i_897_, lean_object* v_entries_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_893_, v_keys_894_, v_vals_895_, v_i_897_, v_entries_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(lean_object* v_00_u03b2_900_, lean_object* v_depth_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_heq_904_, lean_object* v_i_905_, lean_object* v_entries_906_){
_start:
{
size_t v_depth_boxed_907_; lean_object* v_res_908_; 
v_depth_boxed_907_ = lean_unbox_usize(v_depth_901_);
lean_dec(v_depth_901_);
v_res_908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(v_00_u03b2_900_, v_depth_boxed_907_, v_keys_902_, v_vals_903_, v_heq_904_, v_i_905_, v_entries_906_);
lean_dec_ref(v_vals_903_);
lean_dec_ref(v_keys_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_x_910_, v_x_911_, v_x_912_, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(lean_object* v_k_915_, lean_object* v_b_916_, lean_object* v_c_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_apply_7(v_k_915_, v_b_916_, v_c_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(lean_object* v_k_924_, lean_object* v_b_925_, lean_object* v_c_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(v_k_924_, v_b_925_, v_c_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(lean_object* v_e_933_, lean_object* v_k_934_, uint8_t v_cleanupAnnotations_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___f_941_; uint8_t v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___f_941_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_941_, 0, v_k_934_);
v___x_942_ = 1;
v___x_943_ = 0;
v___x_944_ = lean_box(0);
v___x_945_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_933_, v___x_942_, v___x_943_, v___x_942_, v___x_943_, v___x_944_, v___f_941_, v_cleanupAnnotations_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_945_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_945_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_962_, lean_object* v_k_963_, lean_object* v_cleanupAnnotations_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_970_; lean_object* v_res_971_; 
v_cleanupAnnotations_boxed_970_ = lean_unbox(v_cleanupAnnotations_964_);
v_res_971_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_962_, v_k_963_, v_cleanupAnnotations_boxed_970_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(lean_object* v_00_u03b1_972_, lean_object* v_e_973_, lean_object* v_k_974_, uint8_t v_cleanupAnnotations_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_973_, v_k_974_, v_cleanupAnnotations_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___boxed(lean_object* v_00_u03b1_982_, lean_object* v_e_983_, lean_object* v_k_984_, lean_object* v_cleanupAnnotations_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_991_; lean_object* v_res_992_; 
v_cleanupAnnotations_boxed_991_ = lean_unbox(v_cleanupAnnotations_985_);
v_res_992_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(v_00_u03b1_982_, v_e_983_, v_k_984_, v_cleanupAnnotations_boxed_991_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(lean_object* v_mvarId_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_993_, v_x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1000_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg___boxed(lean_object* v_mvarId_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(lean_object* v_00_u03b1_1025_, lean_object* v_mvarId_1026_, lean_object* v_x_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1026_, v_x_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_mvarId_1035_, lean_object* v_x_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(v_00_u03b1_1034_, v_mvarId_1035_, v_x_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t v___x_1043_, uint8_t v___x_1044_, lean_object* v_xs_1045_, lean_object* v_body_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = 1;
v___x_1053_ = l_Lean_Meta_mkForallFVars(v_xs_1045_, v_body_1046_, v___x_1043_, v___x_1044_, v___x_1044_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v_xs_1056_, lean_object* v_body_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v___x_2079__boxed_1063_; uint8_t v___x_2080__boxed_1064_; lean_object* v_res_1065_; 
v___x_2079__boxed_1063_ = lean_unbox(v___x_1054_);
v___x_2080__boxed_1064_ = lean_unbox(v___x_1055_);
v_res_1065_ = l_Lean_MVarId_abstractMVars___lam__0(v___x_2079__boxed_1063_, v___x_2080__boxed_1064_, v_xs_1056_, v_body_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_xs_1056_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object* v_a_1066_, uint8_t v___x_1067_, lean_object* v___f_1068_, lean_object* v_mvarId_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Meta_abstractMVars(v_a_1066_, v___x_1067_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v_mvars_1077_; lean_object* v_expr_1078_; lean_object* v___x_1079_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v_mvars_1077_ = lean_ctor_get(v_a_1076_, 1);
lean_inc_ref(v_mvars_1077_);
v_expr_1078_ = lean_ctor_get(v_a_1076_, 2);
lean_inc_ref(v_expr_1078_);
lean_dec(v_a_1076_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
v___x_1079_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_expr_1078_, v___f_1068_, v___x_1067_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
lean_inc(v_mvarId_1069_);
v___x_1081_ = l_Lean_MVarId_getTag(v_mvarId_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1080_, v_a_1082_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
lean_inc(v_a_1084_);
v___x_1085_ = l_Lean_mkAppN(v_a_1084_, v_mvars_1077_);
lean_dec_ref(v_mvars_1077_);
v___x_1086_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1069_, v___x_1085_, v___y_1071_);
lean_dec(v___y_1071_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1095_);
v___x_1088_ = v___x_1086_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v___x_1086_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = l_Lean_Expr_mvarId_x21(v_a_1084_);
lean_dec(v_a_1084_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_mvars_1077_);
lean_dec(v___y_1071_);
lean_dec(v_mvarId_1069_);
v_a_1096_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1083_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1083_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_a_1080_);
lean_dec_ref(v_mvars_1077_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v_mvarId_1069_);
v_a_1104_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1081_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1081_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v_mvars_1077_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v_mvarId_1069_);
v_a_1112_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1079_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1079_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v_mvarId_1069_);
lean_dec_ref(v___f_1068_);
v_a_1120_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1075_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1075_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object* v_a_1128_, lean_object* v___x_1129_, lean_object* v___f_1130_, lean_object* v_mvarId_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v___x_2105__boxed_1137_; lean_object* v_res_1138_; 
v___x_2105__boxed_1137_ = lean_unbox(v___x_1129_);
v_res_1138_ = l_Lean_MVarId_abstractMVars___lam__1(v_a_1128_, v___x_2105__boxed_1137_, v___f_1130_, v_mvarId_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars(lean_object* v_mvarId_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1139_);
v___x_1146_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1139_, v___x_1145_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref(v___x_1146_);
lean_inc(v_mvarId_1139_);
v___x_1147_ = l_Lean_MVarId_getType(v_mvarId_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1165_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_1148_, v_a_1141_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1165_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1165_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Lean_Expr_hasExprMVar(v_a_1150_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1156_; 
lean_dec(v_a_1150_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_mvarId_1139_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_mvarId_1139_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
else
{
uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
lean_del_object(v___x_1152_);
v___x_1158_ = 0;
v___x_1159_ = lean_box(v___x_1158_);
v___x_1160_ = lean_box(v___x_1154_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1161_, 0, v___x_1159_);
lean_closure_set(v___f_1161_, 1, v___x_1160_);
v___x_1162_ = lean_box(v___x_1158_);
lean_inc(v_mvarId_1139_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1163_, 0, v_a_1150_);
lean_closure_set(v___f_1163_, 1, v___x_1162_);
lean_closure_set(v___f_1163_, 2, v___f_1161_);
lean_closure_set(v___f_1163_, 3, v_mvarId_1139_);
v___x_1164_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1139_, v___f_1163_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_mvarId_1139_);
v_a_1166_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1147_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1147_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_mvarId_1139_);
v_a_1174_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1146_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1146_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___boxed(lean_object* v_mvarId_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_MVarId_abstractMVars(v_mvarId_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object* v_mvarId_1189_, lean_object* v___x_1190_, lean_object* v_f_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
lean_inc(v_mvarId_1189_);
v___x_1197_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1189_, v___x_1190_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v___x_1197_);
lean_inc(v_mvarId_1189_);
v___x_1198_ = l_Lean_MVarId_getTag(v_mvarId_1189_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref(v___x_1198_);
lean_inc(v_mvarId_1189_);
v___x_1200_ = l_Lean_MVarId_getType(v_mvarId_1189_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref(v___x_1200_);
lean_inc(v___y_1195_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc_ref(v___y_1192_);
v___x_1202_ = lean_apply_6(v_f_1191_, v_a_1201_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, lean_box(0));
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1203_, v_a_1199_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref(v___x_1204_);
lean_inc(v_a_1205_);
v___x_1206_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1189_, v_a_1205_, v___y_1193_);
lean_dec(v___y_1193_);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v___x_1206_, 0);
lean_dec(v_unused_1215_);
v___x_1208_ = v___x_1206_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v___x_1206_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = l_Lean_Expr_mvarId_x21(v_a_1205_);
lean_dec(v_a_1205_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v___y_1193_);
lean_dec(v_mvarId_1189_);
v_a_1216_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1204_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1204_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1199_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v_mvarId_1189_);
v_a_1224_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1202_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1202_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1199_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_f_1191_);
lean_dec(v_mvarId_1189_);
v_a_1232_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1200_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1200_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_f_1191_);
lean_dec(v_mvarId_1189_);
v_a_1240_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1198_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1198_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_f_1191_);
lean_dec(v_mvarId_1189_);
v_a_1248_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1197_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1197_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0___boxed(lean_object* v_mvarId_1256_, lean_object* v___x_1257_, lean_object* v_f_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_MVarId_transformTarget___lam__0(v_mvarId_1256_, v___x_1257_, v_f_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object* v_mvarId_1265_, lean_object* v_f_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___f_1273_; lean_object* v___x_1274_; 
v___x_1272_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1265_);
v___f_1273_ = lean_alloc_closure((void*)(l_Lean_MVarId_transformTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1273_, 0, v_mvarId_1265_);
lean_closure_set(v___f_1273_, 1, v___x_1272_);
lean_closure_set(v___f_1273_, 2, v_f_1266_);
v___x_1274_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1265_, v___f_1273_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___boxed(lean_object* v_mvarId_1275_, lean_object* v_f_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_MVarId_transformTarget(v_mvarId_1275_, v_f_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object* v_mvarId_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_MVarId_unfoldReducible___closed__0));
v___x_1291_ = l_Lean_MVarId_transformTarget(v_mvarId_1284_, v___x_1290_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible___boxed(lean_object* v_mvarId_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_MVarId_unfoldReducible(v_mvarId_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object* v_x_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Core_betaReduce(v_x_1299_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_MVarId_betaReduce___lam__0(v_x_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object* v_mvarId_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___f_1320_; lean_object* v___x_1321_; 
v___f_1320_ = ((lean_object*)(l_Lean_MVarId_betaReduce___closed__0));
v___x_1321_ = l_Lean_MVarId_transformTarget(v_mvarId_1314_, v___f_1320_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___boxed(lean_object* v_mvarId_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_MVarId_betaReduce(v_mvarId_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v_res_1328_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = lean_box(0);
v___x_1333_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__1));
v___x_1334_ = l_Lean_mkConst(v___x_1333_, v___x_1332_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__5));
v___x_1342_ = l_Lean_mkConst(v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object* v_mvarId_1343_, lean_object* v___x_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
lean_inc(v_mvarId_1343_);
v___x_1350_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1343_, v___x_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; 
lean_dec_ref(v___x_1350_);
lean_inc(v_mvarId_1343_);
v___x_1351_ = l_Lean_MVarId_getType(v_mvarId_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1406_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1406_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1406_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint8_t v___x_1356_; 
lean_inc(v_a_1352_);
v___x_1356_ = l_Lean_Expr_isFalse(v_a_1352_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_del_object(v___x_1354_);
lean_inc(v_a_1352_);
v___x_1357_ = l_Lean_mkNot(v_a_1352_);
v___x_1358_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__2, &l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
v___x_1359_ = l_Lean_mkArrow(v___x_1357_, v___x_1358_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
lean_inc(v_mvarId_1343_);
v___x_1361_ = l_Lean_MVarId_getTag(v_mvarId_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1360_, v_a_1362_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1376_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__6, &l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6);
lean_inc(v_a_1364_);
v___x_1366_ = l_Lean_mkAppB(v___x_1365_, v_a_1352_, v_a_1364_);
v___x_1367_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1343_, v___x_1366_, v___y_1346_);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1367_, 0);
lean_dec(v_unused_1377_);
v___x_1369_ = v___x_1367_;
v_isShared_1370_ = v_isSharedCheck_1376_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v___x_1367_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1376_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1371_ = l_Lean_Expr_mvarId_x21(v_a_1364_);
lean_dec(v_a_1364_);
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1372_);
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_a_1352_);
lean_dec(v_mvarId_1343_);
v_a_1378_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1363_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1363_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_a_1360_);
lean_dec(v_a_1352_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1345_);
lean_dec(v_mvarId_1343_);
v_a_1386_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1361_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1361_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_a_1352_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1345_);
lean_dec(v_mvarId_1343_);
v_a_1394_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1359_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1359_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec(v_a_1352_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1345_);
lean_dec(v_mvarId_1343_);
v___x_1402_ = lean_box(0);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1402_);
v___x_1404_ = v___x_1354_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1345_);
lean_dec(v_mvarId_1343_);
v_a_1407_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1351_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1351_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1345_);
lean_dec(v_mvarId_1343_);
v_a_1415_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1350_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1350_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object* v_mvarId_1423_, lean_object* v___x_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_MVarId_byContra_x3f___lam__0(v_mvarId_1423_, v___x_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1426_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object* v_mvarId_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; 
v___x_1441_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___closed__1));
lean_inc(v_mvarId_1435_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_MVarId_byContra_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1442_, 0, v_mvarId_1435_);
lean_closure_set(v___f_1442_, 1, v___x_1441_);
v___x_1443_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1435_, v___f_1442_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___boxed(lean_object* v_mvarId_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
return v_res_1450_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0));
v___x_1453_ = l_Lean_stringToMessageData(v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2));
v___x_1456_ = l_Lean_stringToMessageData(v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4));
v___x_1459_ = l_Lean_stringToMessageData(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(lean_object* v_as_x27_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
if (lean_obj_tag(v_as_x27_1460_) == 0)
{
lean_object* v___x_1467_; 
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_b_1461_);
return v___x_1467_;
}
else
{
lean_object* v_head_1468_; lean_object* v_tail_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1523_; 
v_head_1468_ = lean_ctor_get(v_as_x27_1460_, 0);
v_tail_1469_ = lean_ctor_get(v_as_x27_1460_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_as_x27_1460_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1471_ = v_as_x27_1460_;
v_isShared_1472_ = v_isSharedCheck_1523_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_tail_1469_);
lean_inc(v_head_1468_);
lean_dec(v_as_x27_1460_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1523_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; 
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v_head_1468_);
lean_inc(v_b_1461_);
v___x_1473_ = l_Lean_MVarId_clear(v_b_1461_, v_head_1468_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; 
lean_del_object(v___x_1471_);
lean_dec(v_head_1468_);
lean_dec(v_b_1461_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
v_as_x27_1460_ = v_tail_1469_;
v_b_1461_ = v_a_1474_;
goto _start;
}
else
{
lean_object* v_a_1476_; uint8_t v___y_1478_; uint8_t v___x_1521_; 
v_a_1476_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1476_);
v___x_1521_ = l_Lean_Exception_isInterrupt(v_a_1476_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; 
v___x_1522_ = l_Lean_Exception_isRuntime(v_a_1476_);
v___y_1478_ = v___x_1522_;
goto v___jp_1477_;
}
else
{
lean_dec(v_a_1476_);
v___y_1478_ = v___x_1521_;
goto v___jp_1477_;
}
v___jp_1477_:
{
if (v___y_1478_ == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1473_, 0);
lean_dec(v_unused_1520_);
v___x_1480_ = v___x_1473_;
v_isShared_1481_ = v_isSharedCheck_1519_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v___x_1473_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1519_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; 
lean_inc_ref(v___y_1462_);
v___x_1482_ = l_Lean_FVarId_getDecl___redArg(v_head_1468_, v___y_1462_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; uint8_t v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = l_Lean_LocalDecl_isAuxDecl(v_a_1483_);
if (v___x_1484_ == 0)
{
lean_dec(v_a_1483_);
lean_del_object(v___x_1480_);
lean_del_object(v___x_1471_);
v_as_x27_1460_ = v_tail_1469_;
goto _start;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1486_ = l_Lean_LocalDecl_userName(v_a_1483_);
lean_dec(v_a_1483_);
v___x_1487_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_1488_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
v___x_1489_ = l_Lean_MessageData_ofName(v___x_1486_);
lean_inc_ref(v___x_1489_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 7);
lean_ctor_set(v___x_1471_, 1, v___x_1489_);
lean_ctor_set(v___x_1471_, 0, v___x_1488_);
v___x_1491_ = v___x_1471_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1492_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___x_1489_);
v___x_1495_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1496_);
v___x_1498_ = v___x_1480_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; 
lean_inc(v_b_1461_);
v___x_1499_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1487_, v_b_1461_, v___x_1498_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_dec_ref(v___x_1499_);
v_as_x27_1460_ = v_tail_1469_;
goto _start;
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_tail_1469_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_b_1461_);
v_a_1501_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1499_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_del_object(v___x_1480_);
lean_del_object(v___x_1471_);
lean_dec(v_tail_1469_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_b_1461_);
v_a_1511_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1482_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1482_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
else
{
lean_del_object(v___x_1471_);
lean_dec(v_tail_1469_);
lean_dec(v_head_1468_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_b_1461_);
return v___x_1473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(lean_object* v_as_x27_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1524_, v_b_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_1532_, size_t v_sz_1533_, size_t v_i_1534_, lean_object* v_b_1535_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_usize_dec_lt(v_i_1534_, v_sz_1533_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_b_1535_);
return v___x_1538_;
}
else
{
lean_object* v_snd_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1557_; 
v_snd_1539_ = lean_ctor_get(v_b_1535_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_b_1535_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_b_1535_, 0);
lean_dec(v_unused_1558_);
v___x_1541_ = v_b_1535_;
v_isShared_1542_ = v_isSharedCheck_1557_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_snd_1539_);
lean_dec(v_b_1535_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1557_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v_a_1545_; lean_object* v_a_1552_; 
v___x_1543_ = lean_box(0);
v_a_1552_ = lean_array_uget_borrowed(v_as_1532_, v_i_1534_);
if (lean_obj_tag(v_a_1552_) == 0)
{
v_a_1545_ = v_snd_1539_;
goto v___jp_1544_;
}
else
{
lean_object* v_val_1553_; uint8_t v___x_1554_; 
v_val_1553_ = lean_ctor_get(v_a_1552_, 0);
v___x_1554_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1553_);
if (v___x_1554_ == 0)
{
v_a_1545_ = v_snd_1539_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = l_Lean_LocalDecl_fvarId(v_val_1553_);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_snd_1539_);
v_a_1545_ = v___x_1556_;
goto v___jp_1544_;
}
}
v___jp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 1, v_a_1545_);
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1547_ = v___x_1541_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_a_1545_);
v___x_1547_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
size_t v___x_1548_; size_t v___x_1549_; 
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_add(v_i_1534_, v___x_1548_);
v_i_1534_ = v___x_1549_;
v_b_1535_ = v___x_1547_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_1559_, lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_){
_start:
{
size_t v_sz_boxed_1564_; size_t v_i_boxed_1565_; lean_object* v_res_1566_; 
v_sz_boxed_1564_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1565_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1559_, v_sz_boxed_1564_, v_i_boxed_1565_, v_b_1562_);
lean_dec_ref(v_as_1559_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(lean_object* v_as_1567_, size_t v_sz_1568_, size_t v_i_1569_, lean_object* v_b_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_usize_dec_lt(v_i_1569_, v_sz_1568_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_b_1570_);
return v___x_1577_;
}
else
{
lean_object* v_snd_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1596_; 
v_snd_1578_ = lean_ctor_get(v_b_1570_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_b_1570_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_b_1570_, 0);
lean_dec(v_unused_1597_);
v___x_1580_ = v_b_1570_;
v_isShared_1581_ = v_isSharedCheck_1596_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_snd_1578_);
lean_dec(v_b_1570_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1596_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v_a_1584_; lean_object* v_a_1591_; 
v___x_1582_ = lean_box(0);
v_a_1591_ = lean_array_uget_borrowed(v_as_1567_, v_i_1569_);
if (lean_obj_tag(v_a_1591_) == 0)
{
v_a_1584_ = v_snd_1578_;
goto v___jp_1583_;
}
else
{
lean_object* v_val_1592_; uint8_t v___x_1593_; 
v_val_1592_ = lean_ctor_get(v_a_1591_, 0);
v___x_1593_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1592_);
if (v___x_1593_ == 0)
{
v_a_1584_ = v_snd_1578_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = l_Lean_LocalDecl_fvarId(v_val_1592_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_snd_1578_);
v_a_1584_ = v___x_1595_;
goto v___jp_1583_;
}
}
v___jp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v_a_1584_);
lean_ctor_set(v___x_1580_, 0, v___x_1582_);
v___x_1586_ = v___x_1580_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_a_1584_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
size_t v___x_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = ((size_t)1ULL);
v___x_1588_ = lean_usize_add(v_i_1569_, v___x_1587_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1567_, v_sz_1568_, v___x_1588_, v___x_1586_);
return v___x_1589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1598_, lean_object* v_sz_1599_, lean_object* v_i_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
size_t v_sz_boxed_1607_; size_t v_i_boxed_1608_; lean_object* v_res_1609_; 
v_sz_boxed_1607_ = lean_unbox_usize(v_sz_1599_);
lean_dec(v_sz_1599_);
v_i_boxed_1608_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_1598_, v_sz_boxed_1607_, v_i_boxed_1608_, v_b_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_as_1598_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object* v_inh_1610_, lean_object* v_n_1611_, lean_object* v_b_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
if (lean_obj_tag(v_n_1611_) == 0)
{
lean_object* v_cs_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1652_; 
v_cs_1618_ = lean_ctor_get(v_n_1611_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_n_1611_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1620_ = v_n_1611_;
v_isShared_1621_ = v_isSharedCheck_1652_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_cs_1618_);
lean_dec(v_n_1611_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1652_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; size_t v_sz_1624_; size_t v___x_1625_; lean_object* v___x_1626_; 
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v_b_1612_);
v_sz_1624_ = lean_array_size(v_cs_1618_);
v___x_1625_ = ((size_t)0ULL);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_inh_1610_, v_cs_1618_, v_sz_1624_, v___x_1625_, v___x_1623_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec_ref(v_cs_1618_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1643_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v_fst_1631_; 
v_fst_1631_ = lean_ctor_get(v_a_1627_, 0);
if (lean_obj_tag(v_fst_1631_) == 0)
{
lean_object* v_snd_1632_; lean_object* v___x_1634_; 
v_snd_1632_ = lean_ctor_get(v_a_1627_, 1);
lean_inc(v_snd_1632_);
lean_dec(v_a_1627_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 1);
lean_ctor_set(v___x_1620_, 0, v_snd_1632_);
v___x_1634_ = v___x_1620_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_snd_1632_);
v___x_1634_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1634_);
v___x_1636_ = v___x_1629_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_val_1639_; lean_object* v___x_1641_; 
lean_inc_ref(v_fst_1631_);
lean_dec(v_a_1627_);
lean_del_object(v___x_1620_);
v_val_1639_ = lean_ctor_get(v_fst_1631_, 0);
lean_inc(v_val_1639_);
lean_dec_ref(v_fst_1631_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v_val_1639_);
v___x_1641_ = v___x_1629_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_val_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_del_object(v___x_1620_);
v_a_1644_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1626_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1626_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
else
{
lean_object* v_vs_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1687_; 
v_vs_1653_ = lean_ctor_get(v_n_1611_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_n_1611_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1655_ = v_n_1611_;
v_isShared_1656_ = v_isSharedCheck_1687_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_vs_1653_);
lean_dec(v_n_1611_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1687_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v_b_1612_);
v_sz_1659_ = lean_array_size(v_vs_1653_);
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_1653_, v_sz_1659_, v___x_1660_, v___x_1658_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec_ref(v_vs_1653_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1678_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1678_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1678_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_fst_1666_; 
v_fst_1666_ = lean_ctor_get(v_a_1662_, 0);
if (lean_obj_tag(v_fst_1666_) == 0)
{
lean_object* v_snd_1667_; lean_object* v___x_1669_; 
v_snd_1667_ = lean_ctor_get(v_a_1662_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_a_1662_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_snd_1667_);
v___x_1669_ = v___x_1655_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_snd_1667_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1669_);
v___x_1671_ = v___x_1664_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v_val_1674_; lean_object* v___x_1676_; 
lean_inc_ref(v_fst_1666_);
lean_dec(v_a_1662_);
lean_del_object(v___x_1655_);
v_val_1674_ = lean_ctor_get(v_fst_1666_, 0);
lean_inc(v_val_1674_);
lean_dec_ref(v_fst_1666_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v_val_1674_);
v___x_1676_ = v___x_1664_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_val_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_del_object(v___x_1655_);
v_a_1679_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1661_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1661_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object* v_inh_1688_, lean_object* v_as_1689_, size_t v_sz_1690_, size_t v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_lt(v_i_1691_, v_sz_1690_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_b_1692_);
return v___x_1699_;
}
else
{
lean_object* v_snd_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1734_; 
v_snd_1700_ = lean_ctor_get(v_b_1692_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_b_1692_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_b_1692_, 0);
lean_dec(v_unused_1735_);
v___x_1702_ = v_b_1692_;
v_isShared_1703_ = v_isSharedCheck_1734_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_snd_1700_);
lean_dec(v_b_1692_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1734_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_a_1704_; lean_object* v___x_1705_; 
v_a_1704_ = lean_array_uget_borrowed(v_as_1689_, v_i_1691_);
lean_inc(v_snd_1700_);
lean_inc(v_a_1704_);
v___x_1705_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_inh_1688_, v_a_1704_, v_snd_1700_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1725_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
if (lean_obj_tag(v_a_1706_) == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_a_1706_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1710_);
v___x_1712_ = v___x_1702_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_snd_1700_);
v___x_1712_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1712_);
v___x_1714_ = v___x_1708_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
lean_del_object(v___x_1708_);
lean_dec(v_snd_1700_);
v_a_1717_ = lean_ctor_get(v_a_1706_, 0);
lean_inc(v_a_1717_);
lean_dec_ref(v_a_1706_);
v___x_1718_ = lean_box(0);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_a_1717_);
lean_ctor_set(v___x_1702_, 0, v___x_1718_);
v___x_1720_ = v___x_1702_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_a_1717_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
size_t v___x_1721_; size_t v___x_1722_; 
v___x_1721_ = ((size_t)1ULL);
v___x_1722_ = lean_usize_add(v_i_1691_, v___x_1721_);
v_i_1691_ = v___x_1722_;
v_b_1692_ = v___x_1720_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_del_object(v___x_1702_);
lean_dec(v_snd_1700_);
v_a_1726_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1705_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1705_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_1736_, lean_object* v_as_1737_, lean_object* v_sz_1738_, lean_object* v_i_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
size_t v_sz_boxed_1746_; size_t v_i_boxed_1747_; lean_object* v_res_1748_; 
v_sz_boxed_1746_ = lean_unbox_usize(v_sz_1738_);
lean_dec(v_sz_1738_);
v_i_boxed_1747_ = lean_unbox_usize(v_i_1739_);
lean_dec(v_i_1739_);
v_res_1748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_inh_1736_, v_as_1737_, v_sz_boxed_1746_, v_i_boxed_1747_, v_b_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_as_1737_);
lean_dec(v_inh_1736_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object* v_inh_1749_, lean_object* v_n_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_inh_1749_, v_n_1750_, v_b_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v_inh_1749_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1758_, size_t v_sz_1759_, size_t v_i_1760_, lean_object* v_b_1761_){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_usize_dec_lt(v_i_1760_, v_sz_1759_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_b_1761_);
return v___x_1764_;
}
else
{
lean_object* v_snd_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1783_; 
v_snd_1765_ = lean_ctor_get(v_b_1761_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_b_1761_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v_b_1761_, 0);
lean_dec(v_unused_1784_);
v___x_1767_ = v_b_1761_;
v_isShared_1768_ = v_isSharedCheck_1783_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snd_1765_);
lean_dec(v_b_1761_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1783_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v_a_1771_; lean_object* v_a_1778_; 
v___x_1769_ = lean_box(0);
v_a_1778_ = lean_array_uget_borrowed(v_as_1758_, v_i_1760_);
if (lean_obj_tag(v_a_1778_) == 0)
{
v_a_1771_ = v_snd_1765_;
goto v___jp_1770_;
}
else
{
lean_object* v_val_1779_; uint8_t v___x_1780_; 
v_val_1779_ = lean_ctor_get(v_a_1778_, 0);
v___x_1780_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1779_);
if (v___x_1780_ == 0)
{
v_a_1771_ = v_snd_1765_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = l_Lean_LocalDecl_fvarId(v_val_1779_);
v___x_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_snd_1765_);
v_a_1771_ = v___x_1782_;
goto v___jp_1770_;
}
}
v___jp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v_a_1771_);
lean_ctor_set(v___x_1767_, 0, v___x_1769_);
v___x_1773_ = v___x_1767_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_a_1771_);
v___x_1773_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
size_t v___x_1774_; size_t v___x_1775_; 
v___x_1774_ = ((size_t)1ULL);
v___x_1775_ = lean_usize_add(v_i_1760_, v___x_1774_);
v_i_1760_ = v___x_1775_;
v_b_1761_ = v___x_1773_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1785_, lean_object* v_sz_1786_, lean_object* v_i_1787_, lean_object* v_b_1788_, lean_object* v___y_1789_){
_start:
{
size_t v_sz_boxed_1790_; size_t v_i_boxed_1791_; lean_object* v_res_1792_; 
v_sz_boxed_1790_ = lean_unbox_usize(v_sz_1786_);
lean_dec(v_sz_1786_);
v_i_boxed_1791_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1785_, v_sz_boxed_1790_, v_i_boxed_1791_, v_b_1788_);
lean_dec_ref(v_as_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(lean_object* v_as_1793_, size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_b_1796_);
return v___x_1803_;
}
else
{
lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1822_; 
v_snd_1804_ = lean_ctor_get(v_b_1796_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_b_1796_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v_b_1796_, 0);
lean_dec(v_unused_1823_);
v___x_1806_ = v_b_1796_;
v_isShared_1807_ = v_isSharedCheck_1822_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_dec(v_b_1796_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1822_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v_a_1810_; lean_object* v_a_1817_; 
v___x_1808_ = lean_box(0);
v_a_1817_ = lean_array_uget_borrowed(v_as_1793_, v_i_1795_);
if (lean_obj_tag(v_a_1817_) == 0)
{
v_a_1810_ = v_snd_1804_;
goto v___jp_1809_;
}
else
{
lean_object* v_val_1818_; uint8_t v___x_1819_; 
v_val_1818_ = lean_ctor_get(v_a_1817_, 0);
v___x_1819_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1818_);
if (v___x_1819_ == 0)
{
v_a_1810_ = v_snd_1804_;
goto v___jp_1809_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = l_Lean_LocalDecl_fvarId(v_val_1818_);
v___x_1821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v_snd_1804_);
v_a_1810_ = v___x_1821_;
goto v___jp_1809_;
}
}
v___jp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v_a_1810_);
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1812_ = v___x_1806_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_a_1810_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_add(v_i_1795_, v___x_1813_);
v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1793_, v_sz_1794_, v___x_1814_, v___x_1812_);
return v___x_1815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(lean_object* v_as_1824_, lean_object* v_sz_1825_, lean_object* v_i_1826_, lean_object* v_b_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
size_t v_sz_boxed_1833_; size_t v_i_boxed_1834_; lean_object* v_res_1835_; 
v_sz_boxed_1833_ = lean_unbox_usize(v_sz_1825_);
lean_dec(v_sz_1825_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1826_);
lean_dec(v_i_1826_);
v_res_1835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_1824_, v_sz_boxed_1833_, v_i_boxed_1834_, v_b_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v_as_1824_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(lean_object* v_t_1836_, lean_object* v_init_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_root_1843_; lean_object* v_tail_1844_; lean_object* v___x_1845_; 
v_root_1843_ = lean_ctor_get(v_t_1836_, 0);
lean_inc_ref(v_root_1843_);
v_tail_1844_ = lean_ctor_get(v_t_1836_, 1);
lean_inc_ref(v_tail_1844_);
lean_dec_ref(v_t_1836_);
lean_inc(v_init_1837_);
v___x_1845_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1837_, v_root_1843_, v_init_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v_init_1837_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1882_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1882_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1882_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
if (lean_obj_tag(v_a_1846_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; 
lean_dec_ref(v_tail_1844_);
v_a_1850_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v_a_1846_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v_a_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; size_t v_sz_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
lean_del_object(v___x_1848_);
v_a_1854_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_a_1854_);
lean_dec_ref(v_a_1846_);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_a_1854_);
v_sz_1857_ = lean_array_size(v_tail_1844_);
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_1844_, v_sz_1857_, v___x_1858_, v___x_1856_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec_ref(v_tail_1844_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1873_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_fst_1864_; 
v_fst_1864_ = lean_ctor_get(v_a_1860_, 0);
if (lean_obj_tag(v_fst_1864_) == 0)
{
lean_object* v_snd_1865_; lean_object* v___x_1867_; 
v_snd_1865_ = lean_ctor_get(v_a_1860_, 1);
lean_inc(v_snd_1865_);
lean_dec(v_a_1860_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_snd_1865_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_snd_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v_val_1869_; lean_object* v___x_1871_; 
lean_inc_ref(v_fst_1864_);
lean_dec(v_a_1860_);
v_val_1869_ = lean_ctor_get(v_fst_1864_, 0);
lean_inc(v_val_1869_);
lean_dec_ref(v_fst_1864_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_val_1869_);
v___x_1871_ = v___x_1862_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_val_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1859_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1859_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v_tail_1844_);
v_a_1883_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1845_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1845_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(lean_object* v_t_1891_, lean_object* v_init_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_t_1891_, v_init_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0(lean_object* v_mvarId_1899_, lean_object* v___x_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
lean_inc(v_mvarId_1899_);
v___x_1906_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1899_, v___x_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_lctx_1907_; lean_object* v_decls_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_dec_ref(v___x_1906_);
v_lctx_1907_ = lean_ctor_get(v___y_1901_, 2);
v_decls_1908_ = lean_ctor_get(v_lctx_1907_, 1);
v___x_1909_ = lean_box(0);
lean_inc_ref(v_decls_1908_);
v___x_1910_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_decls_1908_, v___x_1909_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1920_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1920_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1920_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
uint8_t v___x_1915_; 
v___x_1915_ = l_List_isEmpty___redArg(v_a_1911_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_del_object(v___x_1913_);
v___x_1916_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_a_1911_, v_mvarId_1899_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
return v___x_1916_;
}
else
{
lean_object* v___x_1918_; 
lean_dec(v_a_1911_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v_mvarId_1899_);
v___x_1918_ = v___x_1913_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_mvarId_1899_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v_mvarId_1899_);
v_a_1921_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1910_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1910_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v_mvarId_1899_);
v_a_1929_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1906_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1906_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0___boxed(lean_object* v_mvarId_1937_, lean_object* v___x_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_MVarId_clearImplDetails___lam__0(v_mvarId_1937_, v___x_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails(lean_object* v_mvarId_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___f_1956_; lean_object* v___x_1957_; 
v___x_1955_ = ((lean_object*)(l_Lean_MVarId_clearImplDetails___closed__1));
lean_inc(v_mvarId_1949_);
v___f_1956_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearImplDetails___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1956_, 0, v_mvarId_1949_);
lean_closure_set(v___f_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1949_, v___f_1956_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___boxed(lean_object* v_mvarId_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_MVarId_clearImplDetails(v_mvarId_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(lean_object* v_as_1965_, lean_object* v_as_x27_1966_, lean_object* v_b_1967_, lean_object* v_a_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1966_, v_b_1967_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___boxed(lean_object* v_as_1975_, lean_object* v_as_x27_1976_, lean_object* v_b_1977_, lean_object* v_a_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(v_as_1975_, v_as_x27_1976_, v_b_1977_, v_a_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v_as_1975_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(lean_object* v_as_1985_, size_t v_sz_1986_, size_t v_i_1987_, lean_object* v_b_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1985_, v_sz_1986_, v_i_1987_, v_b_1988_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1995_, lean_object* v_sz_1996_, lean_object* v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
size_t v_sz_boxed_2004_; size_t v_i_boxed_2005_; lean_object* v_res_2006_; 
v_sz_boxed_2004_ = lean_unbox_usize(v_sz_1996_);
lean_dec(v_sz_1996_);
v_i_boxed_2005_ = lean_unbox_usize(v_i_1997_);
lean_dec(v_i_1997_);
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_1995_, v_sz_boxed_2004_, v_i_boxed_2005_, v_b_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v_as_1995_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_2007_, v_sz_2008_, v_i_2009_, v_b_2010_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_2017_, lean_object* v_sz_2018_, lean_object* v_i_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
size_t v_sz_boxed_2026_; size_t v_i_boxed_2027_; lean_object* v_res_2028_; 
v_sz_boxed_2026_ = lean_unbox_usize(v_sz_2018_);
lean_dec(v_sz_2018_);
v_i_boxed_2027_ = lean_unbox_usize(v_i_2019_);
lean_dec(v_i_2019_);
v_res_2028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_2017_, v_sz_boxed_2026_, v_i_boxed_2027_, v_b_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v_as_2017_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object* v_e_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
switch(lean_obj_tag(v_e_2029_))
{
case 8:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_e_2029_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
case 6:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_e_2029_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
case 10:
{
lean_object* v_expr_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_expr_2037_ = lean_ctor_get(v_e_2029_, 1);
lean_inc_ref(v_expr_2037_);
lean_dec_ref(v_e_2029_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_expr_2037_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
default: 
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_e_2029_);
v___x_2041_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object* v_e_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object* v_e_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_e_2048_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object* v_e_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_object* v_00_u03b1_2059_, lean_object* v_x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_apply_1(v_x_2060_, lean_box(0));
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(v_00_u03b1_2066_, v_x_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_2072_, lean_object* v_x_2073_){
_start:
{
if (lean_obj_tag(v_x_2073_) == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_box(0);
return v___x_2074_;
}
else
{
lean_object* v_key_2075_; lean_object* v_value_2076_; lean_object* v_tail_2077_; uint8_t v___x_2078_; 
v_key_2075_ = lean_ctor_get(v_x_2073_, 0);
v_value_2076_ = lean_ctor_get(v_x_2073_, 1);
v_tail_2077_ = lean_ctor_get(v_x_2073_, 2);
v___x_2078_ = l_Lean_ExprStructEq_beq(v_key_2075_, v_a_2072_);
if (v___x_2078_ == 0)
{
v_x_2073_ = v_tail_2077_;
goto _start;
}
else
{
lean_object* v___x_2080_; 
lean_inc(v_value_2076_);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v_value_2076_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_2081_, lean_object* v_x_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2081_, v_x_2082_);
lean_dec(v_x_2082_);
lean_dec_ref(v_a_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_buckets_2086_; lean_object* v___x_2087_; uint64_t v___x_2088_; uint64_t v___x_2089_; uint64_t v___x_2090_; uint64_t v_fold_2091_; uint64_t v___x_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_buckets_2086_ = lean_ctor_get(v_m_2084_, 1);
v___x_2087_ = lean_array_get_size(v_buckets_2086_);
v___x_2088_ = l_Lean_ExprStructEq_hash(v_a_2085_);
v___x_2089_ = 32ULL;
v___x_2090_ = lean_uint64_shift_right(v___x_2088_, v___x_2089_);
v_fold_2091_ = lean_uint64_xor(v___x_2088_, v___x_2090_);
v___x_2092_ = 16ULL;
v___x_2093_ = lean_uint64_shift_right(v_fold_2091_, v___x_2092_);
v___x_2094_ = lean_uint64_xor(v_fold_2091_, v___x_2093_);
v___x_2095_ = lean_uint64_to_usize(v___x_2094_);
v___x_2096_ = lean_usize_of_nat(v___x_2087_);
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_sub(v___x_2096_, v___x_2097_);
v___x_2099_ = lean_usize_land(v___x_2095_, v___x_2098_);
v___x_2100_ = lean_array_uget_borrowed(v_buckets_2086_, v___x_2099_);
v___x_2101_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2085_, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2102_, v_a_2103_);
lean_dec_ref(v_a_2103_);
lean_dec_ref(v_m_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2105_, lean_object* v_x_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_apply_1(v_x_2106_, lean_box(0));
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2112_, lean_object* v_x_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_2112_, v_x_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2117_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = l_Lean_maxRecDepthErrorMessage;
v___x_2124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_2126_ = l_Lean_MessageData_ofFormat(v___x_2125_);
return v___x_2126_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_2128_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_2129_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_2130_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_ref_2130_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object* v_x_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___y_2144_; lean_object* v_fileName_2153_; lean_object* v_fileMap_2154_; lean_object* v_options_2155_; lean_object* v_currRecDepth_2156_; lean_object* v_maxRecDepth_2157_; lean_object* v_ref_2158_; lean_object* v_currNamespace_2159_; lean_object* v_openDecls_2160_; lean_object* v_initHeartbeats_2161_; lean_object* v_maxHeartbeats_2162_; lean_object* v_quotContext_2163_; lean_object* v_currMacroScope_2164_; uint8_t v_diag_2165_; lean_object* v_cancelTk_x3f_2166_; uint8_t v_suppressElabErrors_2167_; lean_object* v_inheritedTraceOptions_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2180_; 
v_fileName_2153_ = lean_ctor_get(v___y_2140_, 0);
v_fileMap_2154_ = lean_ctor_get(v___y_2140_, 1);
v_options_2155_ = lean_ctor_get(v___y_2140_, 2);
v_currRecDepth_2156_ = lean_ctor_get(v___y_2140_, 3);
v_maxRecDepth_2157_ = lean_ctor_get(v___y_2140_, 4);
v_ref_2158_ = lean_ctor_get(v___y_2140_, 5);
v_currNamespace_2159_ = lean_ctor_get(v___y_2140_, 6);
v_openDecls_2160_ = lean_ctor_get(v___y_2140_, 7);
v_initHeartbeats_2161_ = lean_ctor_get(v___y_2140_, 8);
v_maxHeartbeats_2162_ = lean_ctor_get(v___y_2140_, 9);
v_quotContext_2163_ = lean_ctor_get(v___y_2140_, 10);
v_currMacroScope_2164_ = lean_ctor_get(v___y_2140_, 11);
v_diag_2165_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*14);
v_cancelTk_x3f_2166_ = lean_ctor_get(v___y_2140_, 12);
v_suppressElabErrors_2167_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2168_ = lean_ctor_get(v___y_2140_, 13);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___y_2140_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2170_ = v___y_2140_;
v_isShared_2171_ = v_isSharedCheck_2180_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_inheritedTraceOptions_2168_);
lean_inc(v_cancelTk_x3f_2166_);
lean_inc(v_currMacroScope_2164_);
lean_inc(v_quotContext_2163_);
lean_inc(v_maxHeartbeats_2162_);
lean_inc(v_initHeartbeats_2161_);
lean_inc(v_openDecls_2160_);
lean_inc(v_currNamespace_2159_);
lean_inc(v_ref_2158_);
lean_inc(v_maxRecDepth_2157_);
lean_inc(v_currRecDepth_2156_);
lean_inc(v_options_2155_);
lean_inc(v_fileMap_2154_);
lean_inc(v_fileName_2153_);
lean_dec(v___y_2140_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2180_;
goto v_resetjp_2169_;
}
v___jp_2143_:
{
if (lean_obj_tag(v___y_2144_) == 0)
{
return v___y_2144_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
v_a_2145_ = lean_ctor_get(v___y_2144_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___y_2144_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___y_2144_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___y_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
v_resetjp_2169_:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_eq(v_currRecDepth_2156_, v_maxRecDepth_2157_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_nat_add(v_currRecDepth_2156_, v___x_2173_);
lean_dec(v_currRecDepth_2156_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 3, v___x_2174_);
v___x_2176_ = v___x_2170_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_fileName_2153_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_fileMap_2154_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_options_2155_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_maxRecDepth_2157_);
lean_ctor_set(v_reuseFailAlloc_2178_, 5, v_ref_2158_);
lean_ctor_set(v_reuseFailAlloc_2178_, 6, v_currNamespace_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 7, v_openDecls_2160_);
lean_ctor_set(v_reuseFailAlloc_2178_, 8, v_initHeartbeats_2161_);
lean_ctor_set(v_reuseFailAlloc_2178_, 9, v_maxHeartbeats_2162_);
lean_ctor_set(v_reuseFailAlloc_2178_, 10, v_quotContext_2163_);
lean_ctor_set(v_reuseFailAlloc_2178_, 11, v_currMacroScope_2164_);
lean_ctor_set(v_reuseFailAlloc_2178_, 12, v_cancelTk_x3f_2166_);
lean_ctor_set(v_reuseFailAlloc_2178_, 13, v_inheritedTraceOptions_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*14, v_diag_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*14 + 1, v_suppressElabErrors_2167_);
v___x_2176_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_apply_4(v_x_2138_, v___y_2139_, v___x_2176_, v___y_2141_, lean_box(0));
v___y_2144_ = v___x_2177_;
goto v___jp_2143_;
}
}
else
{
lean_object* v___x_2179_; 
lean_del_object(v___x_2170_);
lean_dec_ref(v_inheritedTraceOptions_2168_);
lean_dec(v_cancelTk_x3f_2166_);
lean_dec(v_currMacroScope_2164_);
lean_dec(v_quotContext_2163_);
lean_dec(v_maxHeartbeats_2162_);
lean_dec(v_initHeartbeats_2161_);
lean_dec(v_openDecls_2160_);
lean_dec(v_currNamespace_2159_);
lean_dec(v_maxRecDepth_2157_);
lean_dec(v_currRecDepth_2156_);
lean_dec_ref(v_options_2155_);
lean_dec_ref(v_fileMap_2154_);
lean_dec_ref(v_fileName_2153_);
lean_dec(v___y_2141_);
lean_dec(v___y_2139_);
lean_dec_ref(v_x_2138_);
v___x_2179_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2158_);
v___y_2144_ = v___x_2179_;
goto v___jp_2143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
if (lean_obj_tag(v_x_2188_) == 0)
{
return v_x_2187_;
}
else
{
lean_object* v_key_2189_; lean_object* v_value_2190_; lean_object* v_tail_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2214_; 
v_key_2189_ = lean_ctor_get(v_x_2188_, 0);
v_value_2190_ = lean_ctor_get(v_x_2188_, 1);
v_tail_2191_ = lean_ctor_get(v_x_2188_, 2);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_x_2188_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2193_ = v_x_2188_;
v_isShared_2194_ = v_isSharedCheck_2214_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_tail_2191_);
lean_inc(v_value_2190_);
lean_inc(v_key_2189_);
lean_dec(v_x_2188_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2214_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; uint64_t v___x_2196_; uint64_t v___x_2197_; uint64_t v___x_2198_; uint64_t v_fold_2199_; uint64_t v___x_2200_; uint64_t v___x_2201_; uint64_t v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2195_ = lean_array_get_size(v_x_2187_);
v___x_2196_ = l_Lean_ExprStructEq_hash(v_key_2189_);
v___x_2197_ = 32ULL;
v___x_2198_ = lean_uint64_shift_right(v___x_2196_, v___x_2197_);
v_fold_2199_ = lean_uint64_xor(v___x_2196_, v___x_2198_);
v___x_2200_ = 16ULL;
v___x_2201_ = lean_uint64_shift_right(v_fold_2199_, v___x_2200_);
v___x_2202_ = lean_uint64_xor(v_fold_2199_, v___x_2201_);
v___x_2203_ = lean_uint64_to_usize(v___x_2202_);
v___x_2204_ = lean_usize_of_nat(v___x_2195_);
v___x_2205_ = ((size_t)1ULL);
v___x_2206_ = lean_usize_sub(v___x_2204_, v___x_2205_);
v___x_2207_ = lean_usize_land(v___x_2203_, v___x_2206_);
v___x_2208_ = lean_array_uget_borrowed(v_x_2187_, v___x_2207_);
lean_inc(v___x_2208_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 2, v___x_2208_);
v___x_2210_ = v___x_2193_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_key_2189_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_value_2190_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_array_uset(v_x_2187_, v___x_2207_, v___x_2210_);
v_x_2187_ = v___x_2211_;
v_x_2188_ = v_tail_2191_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_2215_, lean_object* v_source_2216_, lean_object* v_target_2217_){
_start:
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = lean_array_get_size(v_source_2216_);
v___x_2219_ = lean_nat_dec_lt(v_i_2215_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_dec_ref(v_source_2216_);
lean_dec(v_i_2215_);
return v_target_2217_;
}
else
{
lean_object* v_es_2220_; lean_object* v___x_2221_; lean_object* v_source_2222_; lean_object* v_target_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_es_2220_ = lean_array_fget(v_source_2216_, v_i_2215_);
v___x_2221_ = lean_box(0);
v_source_2222_ = lean_array_fset(v_source_2216_, v_i_2215_, v___x_2221_);
v_target_2223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_2217_, v_es_2220_);
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_nat_add(v_i_2215_, v___x_2224_);
lean_dec(v_i_2215_);
v_i_2215_ = v___x_2225_;
v_source_2216_ = v_source_2222_;
v_target_2217_ = v_target_2223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v_nbuckets_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2228_ = lean_array_get_size(v_data_2227_);
v___x_2229_ = lean_unsigned_to_nat(2u);
v_nbuckets_2230_ = lean_nat_mul(v___x_2228_, v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_mk_array(v_nbuckets_2230_, v___x_2232_);
v___x_2234_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_2231_, v_data_2227_, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_2235_, lean_object* v_x_2236_){
_start:
{
if (lean_obj_tag(v_x_2236_) == 0)
{
uint8_t v___x_2237_; 
v___x_2237_ = 0;
return v___x_2237_;
}
else
{
lean_object* v_key_2238_; lean_object* v_tail_2239_; uint8_t v___x_2240_; 
v_key_2238_ = lean_ctor_get(v_x_2236_, 0);
v_tail_2239_ = lean_ctor_get(v_x_2236_, 2);
v___x_2240_ = l_Lean_ExprStructEq_beq(v_key_2238_, v_a_2235_);
if (v___x_2240_ == 0)
{
v_x_2236_ = v_tail_2239_;
goto _start;
}
else
{
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_2242_, lean_object* v_x_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2242_, v_x_2243_);
lean_dec(v_x_2243_);
lean_dec_ref(v_a_2242_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_2246_, lean_object* v_b_2247_, lean_object* v_x_2248_){
_start:
{
if (lean_obj_tag(v_x_2248_) == 0)
{
lean_dec(v_b_2247_);
lean_dec_ref(v_a_2246_);
return v_x_2248_;
}
else
{
lean_object* v_key_2249_; lean_object* v_value_2250_; lean_object* v_tail_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2263_; 
v_key_2249_ = lean_ctor_get(v_x_2248_, 0);
v_value_2250_ = lean_ctor_get(v_x_2248_, 1);
v_tail_2251_ = lean_ctor_get(v_x_2248_, 2);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_x_2248_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2253_ = v_x_2248_;
v_isShared_2254_ = v_isSharedCheck_2263_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_tail_2251_);
lean_inc(v_value_2250_);
lean_inc(v_key_2249_);
lean_dec(v_x_2248_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2263_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
uint8_t v___x_2255_; 
v___x_2255_ = l_Lean_ExprStructEq_beq(v_key_2249_, v_a_2246_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2246_, v_b_2247_, v_tail_2251_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 2, v___x_2256_);
v___x_2258_ = v___x_2253_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_key_2249_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_value_2250_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
else
{
lean_object* v___x_2261_; 
lean_dec(v_value_2250_);
lean_dec(v_key_2249_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v_b_2247_);
lean_ctor_set(v___x_2253_, 0, v_a_2246_);
v___x_2261_ = v___x_2253_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2246_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_b_2247_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_tail_2251_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object* v_m_2264_, lean_object* v_a_2265_, lean_object* v_b_2266_){
_start:
{
lean_object* v_size_2267_; lean_object* v_buckets_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2311_; 
v_size_2267_ = lean_ctor_get(v_m_2264_, 0);
v_buckets_2268_ = lean_ctor_get(v_m_2264_, 1);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_m_2264_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2270_ = v_m_2264_;
v_isShared_2271_ = v_isSharedCheck_2311_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_buckets_2268_);
lean_inc(v_size_2267_);
lean_dec(v_m_2264_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2311_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; uint64_t v___x_2273_; uint64_t v___x_2274_; uint64_t v___x_2275_; uint64_t v_fold_2276_; uint64_t v___x_2277_; uint64_t v___x_2278_; uint64_t v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; lean_object* v_bkt_2285_; uint8_t v___x_2286_; 
v___x_2272_ = lean_array_get_size(v_buckets_2268_);
v___x_2273_ = l_Lean_ExprStructEq_hash(v_a_2265_);
v___x_2274_ = 32ULL;
v___x_2275_ = lean_uint64_shift_right(v___x_2273_, v___x_2274_);
v_fold_2276_ = lean_uint64_xor(v___x_2273_, v___x_2275_);
v___x_2277_ = 16ULL;
v___x_2278_ = lean_uint64_shift_right(v_fold_2276_, v___x_2277_);
v___x_2279_ = lean_uint64_xor(v_fold_2276_, v___x_2278_);
v___x_2280_ = lean_uint64_to_usize(v___x_2279_);
v___x_2281_ = lean_usize_of_nat(v___x_2272_);
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_sub(v___x_2281_, v___x_2282_);
v___x_2284_ = lean_usize_land(v___x_2280_, v___x_2283_);
v_bkt_2285_ = lean_array_uget_borrowed(v_buckets_2268_, v___x_2284_);
v___x_2286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2265_, v_bkt_2285_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; lean_object* v_size_x27_2288_; lean_object* v___x_2289_; lean_object* v_buckets_x27_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2287_ = lean_unsigned_to_nat(1u);
v_size_x27_2288_ = lean_nat_add(v_size_2267_, v___x_2287_);
lean_dec(v_size_2267_);
lean_inc(v_bkt_2285_);
v___x_2289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2289_, 0, v_a_2265_);
lean_ctor_set(v___x_2289_, 1, v_b_2266_);
lean_ctor_set(v___x_2289_, 2, v_bkt_2285_);
v_buckets_x27_2290_ = lean_array_uset(v_buckets_2268_, v___x_2284_, v___x_2289_);
v___x_2291_ = lean_unsigned_to_nat(4u);
v___x_2292_ = lean_nat_mul(v_size_x27_2288_, v___x_2291_);
v___x_2293_ = lean_unsigned_to_nat(3u);
v___x_2294_ = lean_nat_div(v___x_2292_, v___x_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_array_get_size(v_buckets_x27_2290_);
v___x_2296_ = lean_nat_dec_le(v___x_2294_, v___x_2295_);
lean_dec(v___x_2294_);
if (v___x_2296_ == 0)
{
lean_object* v_val_2297_; lean_object* v___x_2299_; 
v_val_2297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_2290_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v_val_2297_);
lean_ctor_set(v___x_2270_, 0, v_size_x27_2288_);
v___x_2299_ = v___x_2270_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_size_x27_2288_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_val_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
else
{
lean_object* v___x_2302_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v_buckets_x27_2290_);
lean_ctor_set(v___x_2270_, 0, v_size_x27_2288_);
v___x_2302_ = v___x_2270_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_size_x27_2288_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_buckets_x27_2290_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_object* v___x_2304_; lean_object* v_buckets_x27_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
lean_inc(v_bkt_2285_);
v___x_2304_ = lean_box(0);
v_buckets_x27_2305_ = lean_array_uset(v_buckets_2268_, v___x_2284_, v___x_2304_);
v___x_2306_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2265_, v_b_2266_, v_bkt_2285_);
v___x_2307_ = lean_array_uset(v_buckets_x27_2305_, v___x_2284_, v___x_2306_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___x_2307_);
v___x_2309_ = v___x_2270_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_size_2267_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object* v_a_2312_, lean_object* v_e_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_st_ref_take(v_a_2312_);
v___x_2317_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2316_, v_e_2313_, v_a_2314_);
v___x_2318_ = lean_st_ref_set(v_a_2312_, v___x_2317_);
v___x_2319_ = lean_box(0);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2320_, lean_object* v_e_2321_, lean_object* v_a_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2320_, v_e_2321_, v_a_2322_);
lean_dec(v_a_2320_);
return v_res_2324_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2325_; lean_object* v_dummy_2326_; 
v___x_2325_ = lean_box(0);
v_dummy_2326_ = l_Lean_Expr_sort___override(v___x_2325_);
return v_dummy_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object* v_pre_2327_, lean_object* v_post_2328_, size_t v_sz_2329_, size_t v_i_2330_, lean_object* v_bs_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
uint8_t v___x_2336_; 
v___x_2336_ = lean_usize_dec_lt(v_i_2330_, v_sz_2329_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; 
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v_post_2328_);
lean_dec_ref(v_pre_2327_);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v_bs_2331_);
return v___x_2337_;
}
else
{
lean_object* v_v_2338_; lean_object* v___x_2339_; 
v_v_2338_ = lean_array_uget_borrowed(v_bs_2331_, v_i_2330_);
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc(v_v_2338_);
lean_inc_ref(v_post_2328_);
lean_inc_ref(v_pre_2327_);
v___x_2339_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2327_, v_post_2328_, v_v_2338_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v_bs_x27_2342_; size_t v___x_2343_; size_t v___x_2344_; lean_object* v___x_2345_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = lean_unsigned_to_nat(0u);
v_bs_x27_2342_ = lean_array_uset(v_bs_2331_, v_i_2330_, v___x_2341_);
v___x_2343_ = ((size_t)1ULL);
v___x_2344_ = lean_usize_add(v_i_2330_, v___x_2343_);
v___x_2345_ = lean_array_uset(v_bs_x27_2342_, v_i_2330_, v_a_2340_);
v_i_2330_ = v___x_2344_;
v_bs_2331_ = v___x_2345_;
goto _start;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v_bs_2331_);
lean_dec_ref(v_post_2328_);
lean_dec_ref(v_pre_2327_);
v_a_2347_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2339_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2339_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object* v_pre_2355_, lean_object* v_post_2356_, lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v_x_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
if (lean_obj_tag(v_x_2357_) == 5)
{
lean_object* v_fn_2364_; lean_object* v_arg_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_fn_2364_ = lean_ctor_get(v_x_2357_, 0);
lean_inc_ref(v_fn_2364_);
v_arg_2365_ = lean_ctor_get(v_x_2357_, 1);
lean_inc_ref(v_arg_2365_);
lean_dec_ref(v_x_2357_);
v___x_2366_ = lean_array_set(v_x_2358_, v_x_2359_, v_arg_2365_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_sub(v_x_2359_, v___x_2367_);
lean_dec(v_x_2359_);
v_x_2357_ = v_fn_2364_;
v_x_2358_ = v___x_2366_;
v_x_2359_ = v___x_2368_;
goto _start;
}
else
{
lean_object* v___x_2370_; 
lean_dec(v_x_2359_);
lean_inc(v___y_2362_);
lean_inc_ref(v___y_2361_);
lean_inc(v___y_2360_);
lean_inc_ref(v_post_2356_);
lean_inc_ref(v_pre_2355_);
v___x_2370_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2355_, v_post_2356_, v_x_2357_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; size_t v_sz_2372_; size_t v___x_2373_; lean_object* v___x_2374_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
v_sz_2372_ = lean_array_size(v_x_2358_);
v___x_2373_ = ((size_t)0ULL);
lean_inc(v___y_2362_);
lean_inc_ref(v___y_2361_);
lean_inc(v___y_2360_);
lean_inc_ref(v_post_2356_);
lean_inc_ref(v_pre_2355_);
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2355_, v_post_2356_, v_sz_2372_, v___x_2373_, v_x_2358_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l_Lean_mkAppN(v_a_2371_, v_a_2375_);
lean_dec(v_a_2375_);
v___x_2377_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2355_, v_post_2356_, v___x_2376_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2377_;
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_a_2371_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v_post_2356_);
lean_dec_ref(v_pre_2355_);
v_a_2378_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2374_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2374_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v_x_2358_);
lean_dec_ref(v_post_2356_);
lean_dec_ref(v_pre_2355_);
return v___x_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object* v_pre_2386_, lean_object* v_e_2387_, lean_object* v_post_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; uint8_t v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; uint8_t v___y_2414_; lean_object* v___y_2415_; uint8_t v___y_2416_; lean_object* v___y_2424_; lean_object* v___y_2425_; uint8_t v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; uint8_t v___y_2429_; lean_object* v___x_2436_; 
lean_inc_ref(v_pre_2386_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc_ref(v_e_2387_);
v___x_2436_ = lean_apply_4(v_pre_2386_, v_e_2387_, v___y_2390_, v___y_2391_, lean_box(0));
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2526_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2526_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2526_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___y_2442_; 
switch(lean_obj_tag(v_a_2437_))
{
case 0:
{
lean_object* v_e_2516_; lean_object* v___x_2518_; 
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_e_2387_);
lean_dec_ref(v_pre_2386_);
v_e_2516_ = lean_ctor_get(v_a_2437_, 0);
lean_inc_ref(v_e_2516_);
lean_dec_ref(v_a_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_e_2516_);
v___x_2518_ = v___x_2439_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_e_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
case 1:
{
lean_object* v_e_2520_; lean_object* v___x_2521_; 
lean_del_object(v___x_2439_);
lean_dec_ref(v_e_2387_);
v_e_2520_ = lean_ctor_get(v_a_2437_, 0);
lean_inc_ref(v_e_2520_);
lean_dec_ref(v_a_2437_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_e_2520_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v_a_2522_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2523_;
}
else
{
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2521_;
}
}
default: 
{
lean_object* v_e_x3f_2524_; 
lean_del_object(v___x_2439_);
v_e_x3f_2524_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_e_x3f_2524_);
lean_dec_ref(v_a_2437_);
if (lean_obj_tag(v_e_x3f_2524_) == 0)
{
v___y_2442_ = v_e_2387_;
goto v___jp_2441_;
}
else
{
lean_object* v_val_2525_; 
lean_dec_ref(v_e_2387_);
v_val_2525_ = lean_ctor_get(v_e_x3f_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref(v_e_x3f_2524_);
v___y_2442_ = v_val_2525_;
goto v___jp_2441_;
}
}
}
v___jp_2441_:
{
switch(lean_obj_tag(v___y_2442_))
{
case 7:
{
lean_object* v_binderName_2443_; lean_object* v_binderType_2444_; lean_object* v_body_2445_; uint8_t v_binderInfo_2446_; lean_object* v___x_2447_; 
v_binderName_2443_ = lean_ctor_get(v___y_2442_, 0);
lean_inc(v_binderName_2443_);
v_binderType_2444_ = lean_ctor_get(v___y_2442_, 1);
v_body_2445_ = lean_ctor_get(v___y_2442_, 2);
v_binderInfo_2446_ = lean_ctor_get_uint8(v___y_2442_, sizeof(void*)*3 + 8);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_binderType_2444_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_binderType_2444_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2449_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref(v___x_2447_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_body_2445_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_body_2445_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; size_t v___x_2451_; size_t v___x_2452_; uint8_t v___x_2453_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref(v___x_2449_);
v___x_2451_ = lean_ptr_addr(v_binderType_2444_);
v___x_2452_ = lean_ptr_addr(v_a_2448_);
v___x_2453_ = lean_usize_dec_eq(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
v___y_2424_ = v_a_2450_;
v___y_2425_ = v_a_2448_;
v___y_2426_ = v_binderInfo_2446_;
v___y_2427_ = v___y_2442_;
v___y_2428_ = v_binderName_2443_;
v___y_2429_ = v___x_2453_;
goto v___jp_2423_;
}
else
{
size_t v___x_2454_; size_t v___x_2455_; uint8_t v___x_2456_; 
v___x_2454_ = lean_ptr_addr(v_body_2445_);
v___x_2455_ = lean_ptr_addr(v_a_2450_);
v___x_2456_ = lean_usize_dec_eq(v___x_2454_, v___x_2455_);
v___y_2424_ = v_a_2450_;
v___y_2425_ = v_a_2448_;
v___y_2426_ = v_binderInfo_2446_;
v___y_2427_ = v___y_2442_;
v___y_2428_ = v_binderName_2443_;
v___y_2429_ = v___x_2456_;
goto v___jp_2423_;
}
}
else
{
lean_dec(v_a_2448_);
lean_dec(v_binderName_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2449_;
}
}
else
{
lean_dec_ref(v___y_2442_);
lean_dec(v_binderName_2443_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2447_;
}
}
case 6:
{
lean_object* v_binderName_2457_; lean_object* v_binderType_2458_; lean_object* v_body_2459_; uint8_t v_binderInfo_2460_; lean_object* v___x_2461_; 
v_binderName_2457_ = lean_ctor_get(v___y_2442_, 0);
lean_inc(v_binderName_2457_);
v_binderType_2458_ = lean_ctor_get(v___y_2442_, 1);
v_body_2459_ = lean_ctor_get(v___y_2442_, 2);
v_binderInfo_2460_ = lean_ctor_get_uint8(v___y_2442_, sizeof(void*)*3 + 8);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_binderType_2458_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_binderType_2458_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref(v___x_2461_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_body_2459_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_body_2459_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; size_t v___x_2465_; size_t v___x_2466_; uint8_t v___x_2467_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref(v___x_2463_);
v___x_2465_ = lean_ptr_addr(v_binderType_2458_);
v___x_2466_ = lean_ptr_addr(v_a_2462_);
v___x_2467_ = lean_usize_dec_eq(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
v___y_2411_ = v_a_2462_;
v___y_2412_ = v_binderName_2457_;
v___y_2413_ = v_a_2464_;
v___y_2414_ = v_binderInfo_2460_;
v___y_2415_ = v___y_2442_;
v___y_2416_ = v___x_2467_;
goto v___jp_2410_;
}
else
{
size_t v___x_2468_; size_t v___x_2469_; uint8_t v___x_2470_; 
v___x_2468_ = lean_ptr_addr(v_body_2459_);
v___x_2469_ = lean_ptr_addr(v_a_2464_);
v___x_2470_ = lean_usize_dec_eq(v___x_2468_, v___x_2469_);
v___y_2411_ = v_a_2462_;
v___y_2412_ = v_binderName_2457_;
v___y_2413_ = v_a_2464_;
v___y_2414_ = v_binderInfo_2460_;
v___y_2415_ = v___y_2442_;
v___y_2416_ = v___x_2470_;
goto v___jp_2410_;
}
}
else
{
lean_dec(v_a_2462_);
lean_dec(v_binderName_2457_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2463_;
}
}
else
{
lean_dec_ref(v___y_2442_);
lean_dec(v_binderName_2457_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2461_;
}
}
case 8:
{
lean_object* v_declName_2471_; lean_object* v_type_2472_; lean_object* v_value_2473_; lean_object* v_body_2474_; uint8_t v_nondep_2475_; lean_object* v___x_2476_; 
v_declName_2471_ = lean_ctor_get(v___y_2442_, 0);
lean_inc(v_declName_2471_);
v_type_2472_ = lean_ctor_get(v___y_2442_, 1);
v_value_2473_ = lean_ctor_get(v___y_2442_, 2);
v_body_2474_ = lean_ctor_get(v___y_2442_, 3);
lean_inc_ref(v_body_2474_);
v_nondep_2475_ = lean_ctor_get_uint8(v___y_2442_, sizeof(void*)*4 + 8);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_type_2472_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_type_2472_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2476_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_value_2473_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_value_2473_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2480_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2478_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_body_2474_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_body_2474_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; size_t v___x_2482_; size_t v___x_2483_; uint8_t v___x_2484_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref(v___x_2480_);
v___x_2482_ = lean_ptr_addr(v_type_2472_);
v___x_2483_ = lean_ptr_addr(v_a_2477_);
v___x_2484_ = lean_usize_dec_eq(v___x_2482_, v___x_2483_);
if (v___x_2484_ == 0)
{
v___y_2394_ = v_a_2481_;
v___y_2395_ = v_a_2479_;
v___y_2396_ = v_body_2474_;
v___y_2397_ = v_a_2477_;
v___y_2398_ = v___y_2442_;
v___y_2399_ = v_nondep_2475_;
v___y_2400_ = v_declName_2471_;
v___y_2401_ = v___x_2484_;
goto v___jp_2393_;
}
else
{
size_t v___x_2485_; size_t v___x_2486_; uint8_t v___x_2487_; 
v___x_2485_ = lean_ptr_addr(v_value_2473_);
v___x_2486_ = lean_ptr_addr(v_a_2479_);
v___x_2487_ = lean_usize_dec_eq(v___x_2485_, v___x_2486_);
v___y_2394_ = v_a_2481_;
v___y_2395_ = v_a_2479_;
v___y_2396_ = v_body_2474_;
v___y_2397_ = v_a_2477_;
v___y_2398_ = v___y_2442_;
v___y_2399_ = v_nondep_2475_;
v___y_2400_ = v_declName_2471_;
v___y_2401_ = v___x_2487_;
goto v___jp_2393_;
}
}
else
{
lean_dec(v_a_2479_);
lean_dec(v_a_2477_);
lean_dec_ref(v_body_2474_);
lean_dec_ref(v___y_2442_);
lean_dec(v_declName_2471_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2480_;
}
}
else
{
lean_dec(v_a_2477_);
lean_dec_ref(v_body_2474_);
lean_dec_ref(v___y_2442_);
lean_dec(v_declName_2471_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2478_;
}
}
else
{
lean_dec_ref(v_body_2474_);
lean_dec_ref(v___y_2442_);
lean_dec(v_declName_2471_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2476_;
}
}
case 5:
{
lean_object* v_dummy_2488_; lean_object* v_nargs_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_dummy_2488_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_2489_ = l_Lean_Expr_getAppNumArgs(v___y_2442_);
lean_inc(v_nargs_2489_);
v___x_2490_ = lean_mk_array(v_nargs_2489_, v_dummy_2488_);
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_sub(v_nargs_2489_, v___x_2491_);
lean_dec(v_nargs_2489_);
v___x_2493_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2386_, v_post_2388_, v___y_2442_, v___x_2490_, v___x_2492_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2493_;
}
case 10:
{
lean_object* v_data_2494_; lean_object* v_expr_2495_; lean_object* v___x_2496_; 
v_data_2494_ = lean_ctor_get(v___y_2442_, 0);
v_expr_2495_ = lean_ctor_get(v___y_2442_, 1);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_expr_2495_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_expr_2495_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; size_t v___x_2498_; size_t v___x_2499_; uint8_t v___x_2500_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = lean_ptr_addr(v_expr_2495_);
v___x_2499_ = lean_ptr_addr(v_a_2497_);
v___x_2500_ = lean_usize_dec_eq(v___x_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_inc(v_data_2494_);
lean_dec_ref(v___y_2442_);
v___x_2501_ = l_Lean_Expr_mdata___override(v_data_2494_, v_a_2497_);
v___x_2502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2501_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; 
lean_dec(v_a_2497_);
v___x_2503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2442_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2503_;
}
}
else
{
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2496_;
}
}
case 11:
{
lean_object* v_typeName_2504_; lean_object* v_idx_2505_; lean_object* v_struct_2506_; lean_object* v___x_2507_; 
v_typeName_2504_ = lean_ctor_get(v___y_2442_, 0);
v_idx_2505_ = lean_ctor_get(v___y_2442_, 1);
v_struct_2506_ = lean_ctor_get(v___y_2442_, 2);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v_struct_2506_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_struct_2506_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; size_t v___x_2509_; size_t v___x_2510_; uint8_t v___x_2511_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref(v___x_2507_);
v___x_2509_ = lean_ptr_addr(v_struct_2506_);
v___x_2510_ = lean_ptr_addr(v_a_2508_);
v___x_2511_ = lean_usize_dec_eq(v___x_2509_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_inc(v_idx_2505_);
lean_inc(v_typeName_2504_);
lean_dec_ref(v___y_2442_);
v___x_2512_ = l_Lean_Expr_proj___override(v_typeName_2504_, v_idx_2505_, v_a_2508_);
v___x_2513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2512_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2513_;
}
else
{
lean_object* v___x_2514_; 
lean_dec(v_a_2508_);
v___x_2514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2442_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2514_;
}
}
else
{
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2507_;
}
}
default: 
{
lean_object* v___x_2515_; 
v___x_2515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2442_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2515_;
}
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_e_2387_);
lean_dec_ref(v_pre_2386_);
v_a_2527_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2436_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2436_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
v___jp_2393_:
{
if (v___y_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v___y_2398_);
lean_dec_ref(v___y_2396_);
v___x_2402_ = l_Lean_Expr_letE___override(v___y_2400_, v___y_2397_, v___y_2395_, v___y_2394_, v___y_2399_);
v___x_2403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2402_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2403_;
}
else
{
size_t v___x_2404_; size_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = lean_ptr_addr(v___y_2396_);
lean_dec_ref(v___y_2396_);
v___x_2405_ = lean_ptr_addr(v___y_2394_);
v___x_2406_ = lean_usize_dec_eq(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v___y_2398_);
v___x_2407_ = l_Lean_Expr_letE___override(v___y_2400_, v___y_2397_, v___y_2395_, v___y_2394_, v___y_2399_);
v___x_2408_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2407_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; 
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2397_);
lean_dec_ref(v___y_2395_);
lean_dec_ref(v___y_2394_);
v___x_2409_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2398_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2409_;
}
}
}
v___jp_2410_:
{
if (v___y_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v___y_2415_);
v___x_2417_ = l_Lean_Expr_lam___override(v___y_2412_, v___y_2411_, v___y_2413_, v___y_2414_);
v___x_2418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2417_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2418_;
}
else
{
uint8_t v___x_2419_; 
v___x_2419_ = l_Lean_instBEqBinderInfo_beq(v___y_2414_, v___y_2414_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec_ref(v___y_2415_);
v___x_2420_ = l_Lean_Expr_lam___override(v___y_2412_, v___y_2411_, v___y_2413_, v___y_2414_);
v___x_2421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2420_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2421_;
}
else
{
lean_object* v___x_2422_; 
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
v___x_2422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2415_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2422_;
}
}
}
v___jp_2423_:
{
if (v___y_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref(v___y_2427_);
v___x_2430_ = l_Lean_Expr_forallE___override(v___y_2428_, v___y_2425_, v___y_2424_, v___y_2426_);
v___x_2431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2430_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2431_;
}
else
{
uint8_t v___x_2432_; 
v___x_2432_ = l_Lean_instBEqBinderInfo_beq(v___y_2426_, v___y_2426_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec_ref(v___y_2427_);
v___x_2433_ = l_Lean_Expr_forallE___override(v___y_2428_, v___y_2425_, v___y_2424_, v___y_2426_);
v___x_2434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2433_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; 
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2425_);
lean_dec_ref(v___y_2424_);
v___x_2435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2427_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_2535_, lean_object* v_e_2536_, lean_object* v_post_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v_pre_2535_, v_e_2536_, v_post_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object* v_pre_2543_, lean_object* v_post_2544_, lean_object* v_e_2545_, lean_object* v_a_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_inc(v_a_2546_);
v___x_2550_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2550_, 0, lean_box(0));
lean_closure_set(v___x_2550_, 1, lean_box(0));
lean_closure_set(v___x_2550_, 2, v_a_2546_);
v___x_2551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___x_2550_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2582_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2582_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2582_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_2552_, v_e_2545_);
lean_dec(v_a_2552_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___f_2557_; lean_object* v___x_2558_; 
lean_del_object(v___x_2554_);
lean_inc_ref(v_e_2545_);
v___f_2557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_2557_, 0, v_pre_2543_);
lean_closure_set(v___f_2557_, 1, v_e_2545_);
lean_closure_set(v___f_2557_, 2, v_post_2544_);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v_a_2546_);
v___x_2558_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2557_, v_a_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___f_2560_; lean_object* v___x_2561_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref(v___x_2558_);
lean_inc(v_a_2559_);
v___f_2560_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2560_, 0, v_a_2546_);
lean_closure_set(v___f_2560_, 1, v_e_2545_);
lean_closure_set(v___f_2560_, 2, v_a_2559_);
v___x_2561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___f_2560_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v___x_2561_, 0);
lean_dec(v_unused_2569_);
v___x_2563_ = v___x_2561_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_dec(v___x_2561_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v_a_2559_);
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2559_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_a_2559_);
v_a_2570_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2561_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2561_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2545_);
return v___x_2558_;
}
}
else
{
lean_object* v_val_2578_; lean_object* v___x_2580_; 
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2545_);
lean_dec_ref(v_post_2544_);
lean_dec_ref(v_pre_2543_);
v_val_2578_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_val_2578_);
lean_dec_ref(v___x_2556_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v_val_2578_);
v___x_2580_ = v___x_2554_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_val_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2545_);
lean_dec_ref(v_post_2544_);
lean_dec_ref(v_pre_2543_);
v_a_2583_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2551_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2551_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object* v_pre_2591_, lean_object* v_post_2592_, lean_object* v_e_2593_, lean_object* v_a_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
lean_inc_ref(v_post_2592_);
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc_ref(v_e_2593_);
v___x_2598_ = lean_apply_4(v_post_2592_, v_e_2593_, v___y_2595_, v___y_2596_, lean_box(0));
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2617_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2617_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2617_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
switch(lean_obj_tag(v_a_2599_))
{
case 0:
{
lean_object* v_e_2603_; lean_object* v___x_2605_; 
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_e_2593_);
lean_dec_ref(v_post_2592_);
lean_dec_ref(v_pre_2591_);
v_e_2603_ = lean_ctor_get(v_a_2599_, 0);
lean_inc_ref(v_e_2603_);
lean_dec_ref(v_a_2599_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v_e_2603_);
v___x_2605_ = v___x_2601_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_e_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
case 1:
{
lean_object* v_e_2607_; lean_object* v___x_2608_; 
lean_del_object(v___x_2601_);
lean_dec_ref(v_e_2593_);
v_e_2607_ = lean_ctor_get(v_a_2599_, 0);
lean_inc_ref(v_e_2607_);
lean_dec_ref(v_a_2599_);
v___x_2608_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2591_, v_post_2592_, v_e_2607_, v_a_2594_, v___y_2595_, v___y_2596_);
return v___x_2608_;
}
default: 
{
lean_object* v_e_x3f_2609_; 
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_post_2592_);
lean_dec_ref(v_pre_2591_);
v_e_x3f_2609_ = lean_ctor_get(v_a_2599_, 0);
lean_inc(v_e_x3f_2609_);
lean_dec_ref(v_a_2599_);
if (lean_obj_tag(v_e_x3f_2609_) == 0)
{
lean_object* v___x_2611_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v_e_2593_);
v___x_2611_ = v___x_2601_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_e_2593_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
else
{
lean_object* v_val_2613_; lean_object* v___x_2615_; 
lean_dec_ref(v_e_2593_);
v_val_2613_ = lean_ctor_get(v_e_x3f_2609_, 0);
lean_inc(v_val_2613_);
lean_dec_ref(v_e_x3f_2609_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v_val_2613_);
v___x_2615_ = v___x_2601_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_val_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_e_2593_);
lean_dec_ref(v_post_2592_);
lean_dec_ref(v_pre_2591_);
v_a_2618_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2598_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2598_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2626_, lean_object* v_post_2627_, lean_object* v_e_2628_, lean_object* v_a_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2626_, v_post_2627_, v_e_2628_, v_a_2629_, v___y_2630_, v___y_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2634_, lean_object* v_post_2635_, lean_object* v_sz_2636_, lean_object* v_i_2637_, lean_object* v_bs_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
size_t v_sz_boxed_2643_; size_t v_i_boxed_2644_; lean_object* v_res_2645_; 
v_sz_boxed_2643_ = lean_unbox_usize(v_sz_2636_);
lean_dec(v_sz_2636_);
v_i_boxed_2644_ = lean_unbox_usize(v_i_2637_);
lean_dec(v_i_2637_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2634_, v_post_2635_, v_sz_boxed_2643_, v_i_boxed_2644_, v_bs_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_2646_, lean_object* v_post_2647_, lean_object* v_x_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2646_, v_post_2647_, v_x_2648_, v_x_2649_, v_x_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(lean_object* v_pre_2656_, lean_object* v_post_2657_, lean_object* v_e_2658_, lean_object* v_a_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2656_, v_post_2657_, v_e_2658_, v_a_2659_, v___y_2660_, v___y_2661_);
return v_res_2663_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_unsigned_to_nat(16u);
v___x_2666_ = lean_mk_array(v___x_2665_, v___x_2664_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v___x_2667_);
return v___x_2669_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
v___x_2671_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2671_, 0, lean_box(0));
lean_closure_set(v___x_2671_, 1, lean_box(0));
lean_closure_set(v___x_2671_, 2, v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object* v_input_2672_, lean_object* v_pre_2673_, lean_object* v_post_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v_a_2680_; lean_object* v___x_2681_; 
v___x_2678_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_2679_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2678_, v___y_2675_, v___y_2676_);
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2679_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v_a_2680_);
v___x_2681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2673_, v_post_2674_, v_input_2672_, v_a_2680_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2683_, 0, lean_box(0));
lean_closure_set(v___x_2683_, 1, lean_box(0));
lean_closure_set(v___x_2683_, 2, v_a_2680_);
v___x_2684_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2683_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2684_, 0);
lean_dec(v_unused_2692_);
v___x_2686_ = v___x_2684_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v___x_2684_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v_a_2682_);
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2682_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_dec(v_a_2680_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v___x_2681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object* v_input_2693_, lean_object* v_pre_2694_, lean_object* v_post_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2693_, v_pre_2694_, v_post_2695_, v___y_2696_, v___y_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* v_e_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___f_2707_; lean_object* v___x_2708_; 
v___f_2707_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0));
v___x_2708_ = lean_find_expr(v___f_2707_, v_e_2703_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v___x_2709_; 
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_e_2703_);
return v___x_2709_;
}
else
{
lean_object* v_pre_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; 
lean_dec_ref(v___x_2708_);
v_pre_2710_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1));
v___f_2711_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2));
v___x_2712_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_e_2703_, v_pre_2710_, v___f_2711_, v_a_2704_, v_a_2705_);
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object* v_e_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2713_, v_a_2714_, v_a_2715_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2718_, lean_object* v_m_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2719_, v_a_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2722_, lean_object* v_m_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_2722_, v_m_2723_, v_a_2724_);
lean_dec_ref(v_a_2724_);
lean_dec_ref(v_m_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_2726_, lean_object* v_ref_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2727_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_ref_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2732_, v_ref_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_x_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_2745_, v_x_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2752_, lean_object* v_m_2753_, lean_object* v_a_2754_, lean_object* v_b_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2753_, v_a_2754_, v_b_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_2757_, lean_object* v_a_2758_, lean_object* v_x_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2758_, v_x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2761_, lean_object* v_a_2762_, lean_object* v_x_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2761_, v_a_2762_, v_x_2763_);
lean_dec(v_x_2763_);
lean_dec_ref(v_a_2762_);
return v_res_2764_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_2765_, lean_object* v_a_2766_, lean_object* v_x_2767_){
_start:
{
uint8_t v___x_2768_; 
v___x_2768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2766_, v_x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_2769_, lean_object* v_a_2770_, lean_object* v_x_2771_){
_start:
{
uint8_t v_res_2772_; lean_object* v_r_2773_; 
v_res_2772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_2769_, v_a_2770_, v_x_2771_);
lean_dec(v_x_2771_);
lean_dec_ref(v_a_2770_);
v_r_2773_ = lean_box(v_res_2772_);
return v_r_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_2774_, lean_object* v_data_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_data_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_2777_, lean_object* v_a_2778_, lean_object* v_b_2779_, lean_object* v_x_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2778_, v_b_2779_, v_x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_2782_, lean_object* v_i_2783_, lean_object* v_source_2784_, lean_object* v_target_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_2783_, v_source_2784_, v_target_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2787_, lean_object* v_x_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_2788_, v_x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(lean_object* v_cls_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_options_2797_; uint8_t v_hasTrace_2798_; 
v_options_2797_ = lean_ctor_get(v___y_2795_, 2);
v_hasTrace_2798_ = lean_ctor_get_uint8(v_options_2797_, sizeof(void*)*1);
if (v_hasTrace_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec(v_cls_2794_);
v___x_2799_ = lean_box(v_hasTrace_2798_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
else
{
lean_object* v_inheritedTraceOptions_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_inheritedTraceOptions_2801_ = lean_ctor_get(v___y_2795_, 13);
v___x_2802_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__1));
v___x_2803_ = l_Lean_Name_append(v___x_2802_, v_cls_2794_);
v___x_2804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2801_, v_options_2797_, v___x_2803_);
lean_dec(v___x_2803_);
v___x_2805_ = lean_box(v___x_2804_);
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___boxed(lean_object* v_cls_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v_cls_2807_, v___y_2808_);
lean_dec_ref(v___y_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0(lean_object* v_cls_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v_cls_2811_, v___y_2814_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___boxed(lean_object* v_cls_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0(v_cls_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1(lean_object* v_msgData_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; lean_object* v_env_2832_; lean_object* v___x_2833_; lean_object* v_mctx_2834_; lean_object* v_lctx_2835_; lean_object* v_options_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2831_ = lean_st_ref_get(v___y_2829_);
v_env_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc_ref(v_env_2832_);
lean_dec(v___x_2831_);
v___x_2833_ = lean_st_ref_get(v___y_2827_);
v_mctx_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc_ref(v_mctx_2834_);
lean_dec(v___x_2833_);
v_lctx_2835_ = lean_ctor_get(v___y_2826_, 2);
v_options_2836_ = lean_ctor_get(v___y_2828_, 2);
lean_inc_ref(v_options_2836_);
lean_inc_ref(v_lctx_2835_);
v___x_2837_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2837_, 0, v_env_2832_);
lean_ctor_set(v___x_2837_, 1, v_mctx_2834_);
lean_ctor_set(v___x_2837_, 2, v_lctx_2835_);
lean_ctor_set(v___x_2837_, 3, v_options_2836_);
v___x_2838_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v_msgData_2825_);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1___boxed(lean_object* v_msgData_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1(v_msgData_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
return v_res_2846_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2847_; double v___x_2848_; 
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = lean_float_of_nat(v___x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(lean_object* v_cls_2852_, lean_object* v_msg_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_ref_2859_; lean_object* v___x_2860_; lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2905_; 
v_ref_2859_ = lean_ctor_get(v___y_2856_, 5);
v___x_2860_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1(v_msg_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2905_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2905_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v_traceState_2866_; lean_object* v_env_2867_; lean_object* v_nextMacroScope_2868_; lean_object* v_ngen_2869_; lean_object* v_auxDeclNGen_2870_; lean_object* v_cache_2871_; lean_object* v_messages_2872_; lean_object* v_infoState_2873_; lean_object* v_snapshotTasks_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2904_; 
v___x_2865_ = lean_st_ref_take(v___y_2857_);
v_traceState_2866_ = lean_ctor_get(v___x_2865_, 4);
v_env_2867_ = lean_ctor_get(v___x_2865_, 0);
v_nextMacroScope_2868_ = lean_ctor_get(v___x_2865_, 1);
v_ngen_2869_ = lean_ctor_get(v___x_2865_, 2);
v_auxDeclNGen_2870_ = lean_ctor_get(v___x_2865_, 3);
v_cache_2871_ = lean_ctor_get(v___x_2865_, 5);
v_messages_2872_ = lean_ctor_get(v___x_2865_, 6);
v_infoState_2873_ = lean_ctor_get(v___x_2865_, 7);
v_snapshotTasks_2874_ = lean_ctor_get(v___x_2865_, 8);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2876_ = v___x_2865_;
v_isShared_2877_ = v_isSharedCheck_2904_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_snapshotTasks_2874_);
lean_inc(v_infoState_2873_);
lean_inc(v_messages_2872_);
lean_inc(v_cache_2871_);
lean_inc(v_traceState_2866_);
lean_inc(v_auxDeclNGen_2870_);
lean_inc(v_ngen_2869_);
lean_inc(v_nextMacroScope_2868_);
lean_inc(v_env_2867_);
lean_dec(v___x_2865_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2904_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
uint64_t v_tid_2878_; lean_object* v_traces_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2903_; 
v_tid_2878_ = lean_ctor_get_uint64(v_traceState_2866_, sizeof(void*)*1);
v_traces_2879_ = lean_ctor_get(v_traceState_2866_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_traceState_2866_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2881_ = v_traceState_2866_;
v_isShared_2882_ = v_isSharedCheck_2903_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_traces_2879_);
lean_dec(v_traceState_2866_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2903_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; double v___x_2884_; uint8_t v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0);
v___x_2885_ = 0;
v___x_2886_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__1));
v___x_2887_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2887_, 0, v_cls_2852_);
lean_ctor_set(v___x_2887_, 1, v___x_2883_);
lean_ctor_set(v___x_2887_, 2, v___x_2886_);
lean_ctor_set_float(v___x_2887_, sizeof(void*)*3, v___x_2884_);
lean_ctor_set_float(v___x_2887_, sizeof(void*)*3 + 8, v___x_2884_);
lean_ctor_set_uint8(v___x_2887_, sizeof(void*)*3 + 16, v___x_2885_);
v___x_2888_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__2));
v___x_2889_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v_a_2861_);
lean_ctor_set(v___x_2889_, 2, v___x_2888_);
lean_inc(v_ref_2859_);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_ref_2859_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = l_Lean_PersistentArray_push___redArg(v_traces_2879_, v___x_2890_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2891_);
v___x_2893_ = v___x_2881_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2891_);
lean_ctor_set_uint64(v_reuseFailAlloc_2902_, sizeof(void*)*1, v_tid_2878_);
v___x_2893_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2895_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 4, v___x_2893_);
v___x_2895_ = v___x_2876_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_env_2867_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_nextMacroScope_2868_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_ngen_2869_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v_auxDeclNGen_2870_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2901_, 5, v_cache_2871_);
lean_ctor_set(v_reuseFailAlloc_2901_, 6, v_messages_2872_);
lean_ctor_set(v_reuseFailAlloc_2901_, 7, v_infoState_2873_);
lean_ctor_set(v_reuseFailAlloc_2901_, 8, v_snapshotTasks_2874_);
v___x_2895_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2896_ = lean_st_ref_set(v___y_2857_, v___x_2895_);
v___x_2897_ = lean_box(0);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2897_);
v___x_2899_ = v___x_2863_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___boxed(lean_object* v_cls_2906_, lean_object* v_msg_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(v_cls_2906_, v_msg_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2913_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_2920_ = l_Lean_stringToMessageData(v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__4));
v___x_2923_ = l_Lean_stringToMessageData(v___x_2922_);
return v___x_2923_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__6(void){
_start:
{
uint8_t v___x_2924_; uint64_t v___x_2925_; 
v___x_2924_ = 1;
v___x_2925_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2924_);
return v___x_2925_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__7));
v___x_2928_ = l_Lean_stringToMessageData(v___x_2927_);
return v___x_2928_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__9));
v___x_2931_ = l_Lean_stringToMessageData(v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0(lean_object* v_e_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
if (lean_obj_tag(v_e_2932_) == 11)
{
lean_object* v_typeName_2944_; lean_object* v_idx_2945_; lean_object* v_struct_2946_; lean_object* v___x_2947_; lean_object* v_env_2948_; lean_object* v___x_2949_; 
v_typeName_2944_ = lean_ctor_get(v_e_2932_, 0);
v_idx_2945_ = lean_ctor_get(v_e_2932_, 1);
v_struct_2946_ = lean_ctor_get(v_e_2932_, 2);
v___x_2947_ = lean_st_ref_get(v___y_2936_);
v_env_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc_ref(v_env_2948_);
lean_dec(v___x_2947_);
lean_inc(v_typeName_2944_);
v___x_2949_ = l_Lean_getStructureInfo_x3f(v_env_2948_, v_typeName_2944_);
if (lean_obj_tag(v___x_2949_) == 1)
{
lean_object* v_val_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3064_; 
v_val_2950_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_2952_ = v___x_2949_;
v_isShared_2953_ = v_isSharedCheck_3064_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_val_2950_);
lean_dec(v___x_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3064_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_fieldNames_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v_fieldNames_2954_ = lean_ctor_get(v_val_2950_, 1);
lean_inc_ref(v_fieldNames_2954_);
lean_dec(v_val_2950_);
v___x_2955_ = lean_array_get_size(v_fieldNames_2954_);
v___x_2956_ = lean_nat_dec_lt(v_idx_2945_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2984_; 
lean_dec_ref(v_fieldNames_2954_);
lean_del_object(v___x_2952_);
v___x_2957_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__1));
v___x_2958_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v___x_2957_, v___y_2935_);
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2984_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2984_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
uint8_t v___x_2963_; 
v___x_2963_ = lean_unbox(v_a_2959_);
lean_dec(v_a_2959_);
if (v___x_2963_ == 0)
{
lean_del_object(v___x_2961_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
goto v___jp_2938_;
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2964_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__3, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__3);
lean_inc(v_idx_2945_);
v___x_2965_ = l_Nat_reprFast(v_idx_2945_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set_tag(v___x_2961_, 3);
lean_ctor_set(v___x_2961_, 0, v___x_2965_);
v___x_2967_ = v___x_2961_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2968_ = l_Lean_MessageData_ofFormat(v___x_2967_);
v___x_2969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2964_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__5, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
lean_inc_ref(v_e_2932_);
v___x_2972_ = l_Lean_indentExpr(v_e_2932_);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(v___x_2957_, v___x_2973_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_dec_ref(v___x_2974_);
goto v___jp_2938_;
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v_e_2932_);
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2985_; uint8_t v_foApprox_2986_; uint8_t v_ctxApprox_2987_; uint8_t v_quasiPatternApprox_2988_; uint8_t v_constApprox_2989_; uint8_t v_isDefEqStuckEx_2990_; uint8_t v_unificationHints_2991_; uint8_t v_proofIrrelevance_2992_; uint8_t v_assignSyntheticOpaque_2993_; uint8_t v_offsetCnstrs_2994_; uint8_t v_etaStruct_2995_; uint8_t v_univApprox_2996_; uint8_t v_iota_2997_; uint8_t v_beta_2998_; uint8_t v_proj_2999_; uint8_t v_zeta_3000_; uint8_t v_zetaDelta_3001_; uint8_t v_zetaUnused_3002_; uint8_t v_zetaHave_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3063_; 
lean_inc_ref(v_struct_2946_);
lean_inc(v_idx_2945_);
lean_dec_ref(v_e_2932_);
v___x_2985_ = l_Lean_Meta_Context_config(v___y_2933_);
v_foApprox_2986_ = lean_ctor_get_uint8(v___x_2985_, 0);
v_ctxApprox_2987_ = lean_ctor_get_uint8(v___x_2985_, 1);
v_quasiPatternApprox_2988_ = lean_ctor_get_uint8(v___x_2985_, 2);
v_constApprox_2989_ = lean_ctor_get_uint8(v___x_2985_, 3);
v_isDefEqStuckEx_2990_ = lean_ctor_get_uint8(v___x_2985_, 4);
v_unificationHints_2991_ = lean_ctor_get_uint8(v___x_2985_, 5);
v_proofIrrelevance_2992_ = lean_ctor_get_uint8(v___x_2985_, 6);
v_assignSyntheticOpaque_2993_ = lean_ctor_get_uint8(v___x_2985_, 7);
v_offsetCnstrs_2994_ = lean_ctor_get_uint8(v___x_2985_, 8);
v_etaStruct_2995_ = lean_ctor_get_uint8(v___x_2985_, 10);
v_univApprox_2996_ = lean_ctor_get_uint8(v___x_2985_, 11);
v_iota_2997_ = lean_ctor_get_uint8(v___x_2985_, 12);
v_beta_2998_ = lean_ctor_get_uint8(v___x_2985_, 13);
v_proj_2999_ = lean_ctor_get_uint8(v___x_2985_, 14);
v_zeta_3000_ = lean_ctor_get_uint8(v___x_2985_, 15);
v_zetaDelta_3001_ = lean_ctor_get_uint8(v___x_2985_, 16);
v_zetaUnused_3002_ = lean_ctor_get_uint8(v___x_2985_, 17);
v_zetaHave_3003_ = lean_ctor_get_uint8(v___x_2985_, 18);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3005_ = v___x_2985_;
v_isShared_3006_ = v_isSharedCheck_3063_;
goto v_resetjp_3004_;
}
else
{
lean_dec(v___x_2985_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3063_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
uint8_t v_trackZetaDelta_3007_; lean_object* v_zetaDeltaSet_3008_; lean_object* v_lctx_3009_; lean_object* v_localInstances_3010_; lean_object* v_defEqCtx_x3f_3011_; lean_object* v_synthPendingDepth_3012_; lean_object* v_canUnfold_x3f_3013_; uint8_t v_univApprox_3014_; uint8_t v_inTypeClassResolution_3015_; uint8_t v_cacheInferType_3016_; uint8_t v___x_3017_; lean_object* v_config_3019_; 
v_trackZetaDelta_3007_ = lean_ctor_get_uint8(v___y_2933_, sizeof(void*)*7);
v_zetaDeltaSet_3008_ = lean_ctor_get(v___y_2933_, 1);
lean_inc(v_zetaDeltaSet_3008_);
v_lctx_3009_ = lean_ctor_get(v___y_2933_, 2);
lean_inc_ref(v_lctx_3009_);
v_localInstances_3010_ = lean_ctor_get(v___y_2933_, 3);
lean_inc_ref(v_localInstances_3010_);
v_defEqCtx_x3f_3011_ = lean_ctor_get(v___y_2933_, 4);
lean_inc(v_defEqCtx_x3f_3011_);
v_synthPendingDepth_3012_ = lean_ctor_get(v___y_2933_, 5);
lean_inc(v_synthPendingDepth_3012_);
v_canUnfold_x3f_3013_ = lean_ctor_get(v___y_2933_, 6);
lean_inc(v_canUnfold_x3f_3013_);
v_univApprox_3014_ = lean_ctor_get_uint8(v___y_2933_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3015_ = lean_ctor_get_uint8(v___y_2933_, sizeof(void*)*7 + 2);
v_cacheInferType_3016_ = lean_ctor_get_uint8(v___y_2933_, sizeof(void*)*7 + 3);
v___x_3017_ = 1;
if (v_isShared_3006_ == 0)
{
v_config_3019_ = v___x_3005_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 0, v_foApprox_2986_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 1, v_ctxApprox_2987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 2, v_quasiPatternApprox_2988_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 3, v_constApprox_2989_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 4, v_isDefEqStuckEx_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 5, v_unificationHints_2991_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 6, v_proofIrrelevance_2992_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 7, v_assignSyntheticOpaque_2993_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 8, v_offsetCnstrs_2994_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 10, v_etaStruct_2995_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 11, v_univApprox_2996_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 12, v_iota_2997_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 13, v_beta_2998_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 14, v_proj_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 15, v_zeta_3000_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 16, v_zetaDelta_3001_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 17, v_zetaUnused_3002_);
lean_ctor_set_uint8(v_reuseFailAlloc_3062_, 18, v_zetaHave_3003_);
v_config_3019_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
uint64_t v___x_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3054_; 
lean_ctor_set_uint8(v_config_3019_, 9, v___x_3017_);
v___x_3020_ = l_Lean_Meta_Context_configKey(v___y_2933_);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___y_2933_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; lean_object* v_unused_3056_; lean_object* v_unused_3057_; lean_object* v_unused_3058_; lean_object* v_unused_3059_; lean_object* v_unused_3060_; lean_object* v_unused_3061_; 
v_unused_3055_ = lean_ctor_get(v___y_2933_, 6);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v___y_2933_, 5);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v___y_2933_, 4);
lean_dec(v_unused_3057_);
v_unused_3058_ = lean_ctor_get(v___y_2933_, 3);
lean_dec(v_unused_3058_);
v_unused_3059_ = lean_ctor_get(v___y_2933_, 2);
lean_dec(v_unused_3059_);
v_unused_3060_ = lean_ctor_get(v___y_2933_, 1);
lean_dec(v_unused_3060_);
v_unused_3061_ = lean_ctor_get(v___y_2933_, 0);
lean_dec(v_unused_3061_);
v___x_3022_ = v___y_2933_;
v_isShared_3023_ = v_isSharedCheck_3054_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v___y_2933_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3054_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
uint64_t v___x_3024_; uint64_t v___x_3025_; lean_object* v___x_3026_; uint64_t v___x_3027_; uint64_t v___x_3028_; uint64_t v_key_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3024_ = 2ULL;
v___x_3025_ = lean_uint64_shift_right(v___x_3020_, v___x_3024_);
v___x_3026_ = lean_array_fget(v_fieldNames_2954_, v_idx_2945_);
lean_dec(v_idx_2945_);
lean_dec_ref(v_fieldNames_2954_);
v___x_3027_ = lean_uint64_shift_left(v___x_3025_, v___x_3024_);
v___x_3028_ = lean_uint64_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__6, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__6_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__6);
v_key_3029_ = lean_uint64_lor(v___x_3027_, v___x_3028_);
v___x_3030_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3030_, 0, v_config_3019_);
lean_ctor_set_uint64(v___x_3030_, sizeof(void*)*1, v_key_3029_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3030_);
v___x_3032_ = v___x_3022_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_zetaDeltaSet_3008_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_lctx_3009_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_localInstances_3010_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v_defEqCtx_x3f_3011_);
lean_ctor_set(v_reuseFailAlloc_3053_, 5, v_synthPendingDepth_3012_);
lean_ctor_set(v_reuseFailAlloc_3053_, 6, v_canUnfold_x3f_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, sizeof(void*)*7, v_trackZetaDelta_3007_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, sizeof(void*)*7 + 1, v_univApprox_3014_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3015_);
lean_ctor_set_uint8(v_reuseFailAlloc_3053_, sizeof(void*)*7 + 3, v_cacheInferType_3016_);
v___x_3032_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_Meta_mkProjection(v_struct_2946_, v___x_3026_, v___x_3032_, v___y_2934_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3044_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3044_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3044_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v_a_3034_);
v___x_3039_ = v___x_2952_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3041_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3039_);
v___x_3041_ = v___x_3036_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_del_object(v___x_2952_);
v_a_3045_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3033_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3033_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
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
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v_a_3067_; uint8_t v___x_3068_; 
lean_dec(v___x_2949_);
v___x_3065_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__1));
v___x_3066_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v___x_3065_, v___y_2935_);
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref(v___x_3066_);
v___x_3068_ = lean_unbox(v_a_3067_);
lean_dec(v_a_3067_);
if (v___x_3068_ == 0)
{
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
goto v___jp_2941_;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3069_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__8, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__8_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__8);
lean_inc(v_typeName_2944_);
v___x_3070_ = l_Lean_MessageData_ofName(v_typeName_2944_);
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__10, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__10_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10);
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3071_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
lean_inc_ref(v_e_2932_);
v___x_3074_ = l_Lean_indentExpr(v_e_2932_);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(v___x_3065_, v___x_3075_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_dec_ref(v___x_3076_);
goto v___jp_2941_;
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec_ref(v_e_2932_);
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3076_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3076_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
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
}
}
else
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_e_2932_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
v___jp_2938_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_e_2932_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
v___jp_2941_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_e_2932_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object* v_e_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Meta_Grind_foldProjs___lam__0(v_e_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object* v_x_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object* v_x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_Meta_Grind_foldProjs___lam__1(v_x_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec_ref(v_x_3104_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_object* v_00_u03b1_3111_, lean_object* v_x_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_apply_1(v_x_3112_, lean_box(0));
v___x_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0___boxed(lean_object* v_00_u03b1_3120_, lean_object* v_x_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(v_00_u03b1_3120_, v_x_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0(lean_object* v_k_3128_, lean_object* v___y_3129_, lean_object* v_b_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_apply_7(v_k_3128_, v_b_3130_, v___y_3129_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, lean_box(0));
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_3137_, lean_object* v___y_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0(v_k_3137_, v___y_3138_, v_b_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_name_3146_, lean_object* v_type_3147_, lean_object* v_val_3148_, lean_object* v_k_3149_, uint8_t v_nondep_3150_, uint8_t v_kind_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___f_3158_; lean_object* v___x_3159_; 
v___f_3158_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3158_, 0, v_k_3149_);
lean_closure_set(v___f_3158_, 1, v___y_3152_);
v___x_3159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3146_, v_type_3147_, v_val_3148_, v___f_3158_, v_nondep_3150_, v_kind_3151_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3159_) == 0)
{
return v___x_3159_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_name_3168_, lean_object* v_type_3169_, lean_object* v_val_3170_, lean_object* v_k_3171_, lean_object* v_nondep_3172_, lean_object* v_kind_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v_nondep_boxed_3180_; uint8_t v_kind_boxed_3181_; lean_object* v_res_3182_; 
v_nondep_boxed_3180_ = lean_unbox(v_nondep_3172_);
v_kind_boxed_3181_ = lean_unbox(v_kind_3173_);
v_res_3182_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(v_name_3168_, v_type_3169_, v_val_3170_, v_k_3171_, v_nondep_boxed_3180_, v_kind_boxed_3181_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(lean_object* v_name_3183_, uint8_t v_bi_3184_, lean_object* v_type_3185_, lean_object* v_k_3186_, uint8_t v_kind_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___f_3194_; lean_object* v___x_3195_; 
v___f_3194_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3194_, 0, v_k_3186_);
lean_closure_set(v___f_3194_, 1, v___y_3188_);
v___x_3195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3183_, v_bi_3184_, v_type_3185_, v___f_3194_, v_kind_3187_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3195_) == 0)
{
return v___x_3195_;
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_name_3204_, lean_object* v_bi_3205_, lean_object* v_type_3206_, lean_object* v_k_3207_, lean_object* v_kind_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
uint8_t v_bi_boxed_3215_; uint8_t v_kind_boxed_3216_; lean_object* v_res_3217_; 
v_bi_boxed_3215_ = lean_unbox(v_bi_3205_);
v_kind_boxed_3216_ = lean_unbox(v_kind_3208_);
v_res_3217_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_name_3204_, v_bi_boxed_3215_, v_type_3206_, v_k_3207_, v_kind_boxed_3216_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2(lean_object* v___x_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3218_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2(v___x_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(lean_object* v_ref_3232_){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_ref_3232_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg___boxed(lean_object* v_ref_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(v_ref_3237_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(lean_object* v_x_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___y_3248_; lean_object* v_fileName_3257_; lean_object* v_fileMap_3258_; lean_object* v_options_3259_; lean_object* v_currRecDepth_3260_; lean_object* v_maxRecDepth_3261_; lean_object* v_ref_3262_; lean_object* v_currNamespace_3263_; lean_object* v_openDecls_3264_; lean_object* v_initHeartbeats_3265_; lean_object* v_maxHeartbeats_3266_; lean_object* v_quotContext_3267_; lean_object* v_currMacroScope_3268_; uint8_t v_diag_3269_; lean_object* v_cancelTk_x3f_3270_; uint8_t v_suppressElabErrors_3271_; lean_object* v_inheritedTraceOptions_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3284_; 
v_fileName_3257_ = lean_ctor_get(v___y_3244_, 0);
v_fileMap_3258_ = lean_ctor_get(v___y_3244_, 1);
v_options_3259_ = lean_ctor_get(v___y_3244_, 2);
v_currRecDepth_3260_ = lean_ctor_get(v___y_3244_, 3);
v_maxRecDepth_3261_ = lean_ctor_get(v___y_3244_, 4);
v_ref_3262_ = lean_ctor_get(v___y_3244_, 5);
v_currNamespace_3263_ = lean_ctor_get(v___y_3244_, 6);
v_openDecls_3264_ = lean_ctor_get(v___y_3244_, 7);
v_initHeartbeats_3265_ = lean_ctor_get(v___y_3244_, 8);
v_maxHeartbeats_3266_ = lean_ctor_get(v___y_3244_, 9);
v_quotContext_3267_ = lean_ctor_get(v___y_3244_, 10);
v_currMacroScope_3268_ = lean_ctor_get(v___y_3244_, 11);
v_diag_3269_ = lean_ctor_get_uint8(v___y_3244_, sizeof(void*)*14);
v_cancelTk_x3f_3270_ = lean_ctor_get(v___y_3244_, 12);
v_suppressElabErrors_3271_ = lean_ctor_get_uint8(v___y_3244_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3272_ = lean_ctor_get(v___y_3244_, 13);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___y_3244_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3274_ = v___y_3244_;
v_isShared_3275_ = v_isSharedCheck_3284_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_inheritedTraceOptions_3272_);
lean_inc(v_cancelTk_x3f_3270_);
lean_inc(v_currMacroScope_3268_);
lean_inc(v_quotContext_3267_);
lean_inc(v_maxHeartbeats_3266_);
lean_inc(v_initHeartbeats_3265_);
lean_inc(v_openDecls_3264_);
lean_inc(v_currNamespace_3263_);
lean_inc(v_ref_3262_);
lean_inc(v_maxRecDepth_3261_);
lean_inc(v_currRecDepth_3260_);
lean_inc(v_options_3259_);
lean_inc(v_fileMap_3258_);
lean_inc(v_fileName_3257_);
lean_dec(v___y_3244_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3284_;
goto v_resetjp_3273_;
}
v___jp_3247_:
{
if (lean_obj_tag(v___y_3248_) == 0)
{
return v___y_3248_;
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_a_3249_ = lean_ctor_get(v___y_3248_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___y_3248_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___y_3248_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___y_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
v_resetjp_3273_:
{
uint8_t v___x_3276_; 
v___x_3276_ = lean_nat_dec_eq(v_currRecDepth_3260_, v_maxRecDepth_3261_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3277_ = lean_unsigned_to_nat(1u);
v___x_3278_ = lean_nat_add(v_currRecDepth_3260_, v___x_3277_);
lean_dec(v_currRecDepth_3260_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 3, v___x_3278_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_fileName_3257_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_fileMap_3258_);
lean_ctor_set(v_reuseFailAlloc_3282_, 2, v_options_3259_);
lean_ctor_set(v_reuseFailAlloc_3282_, 3, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3282_, 4, v_maxRecDepth_3261_);
lean_ctor_set(v_reuseFailAlloc_3282_, 5, v_ref_3262_);
lean_ctor_set(v_reuseFailAlloc_3282_, 6, v_currNamespace_3263_);
lean_ctor_set(v_reuseFailAlloc_3282_, 7, v_openDecls_3264_);
lean_ctor_set(v_reuseFailAlloc_3282_, 8, v_initHeartbeats_3265_);
lean_ctor_set(v_reuseFailAlloc_3282_, 9, v_maxHeartbeats_3266_);
lean_ctor_set(v_reuseFailAlloc_3282_, 10, v_quotContext_3267_);
lean_ctor_set(v_reuseFailAlloc_3282_, 11, v_currMacroScope_3268_);
lean_ctor_set(v_reuseFailAlloc_3282_, 12, v_cancelTk_x3f_3270_);
lean_ctor_set(v_reuseFailAlloc_3282_, 13, v_inheritedTraceOptions_3272_);
lean_ctor_set_uint8(v_reuseFailAlloc_3282_, sizeof(void*)*14, v_diag_3269_);
lean_ctor_set_uint8(v_reuseFailAlloc_3282_, sizeof(void*)*14 + 1, v_suppressElabErrors_3271_);
v___x_3280_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_apply_6(v_x_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___x_3280_, v___y_3245_, lean_box(0));
v___y_3248_ = v___x_3281_;
goto v___jp_3247_;
}
}
else
{
lean_object* v___x_3283_; 
lean_del_object(v___x_3274_);
lean_dec_ref(v_inheritedTraceOptions_3272_);
lean_dec(v_cancelTk_x3f_3270_);
lean_dec(v_currMacroScope_3268_);
lean_dec(v_quotContext_3267_);
lean_dec(v_maxHeartbeats_3266_);
lean_dec(v_initHeartbeats_3265_);
lean_dec(v_openDecls_3264_);
lean_dec(v_currNamespace_3263_);
lean_dec(v_maxRecDepth_3261_);
lean_dec(v_currRecDepth_3260_);
lean_dec_ref(v_options_3259_);
lean_dec_ref(v_fileMap_3258_);
lean_dec_ref(v_fileName_3257_);
lean_dec(v___y_3245_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v_x_3240_);
v___x_3283_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(v_ref_3262_);
v___y_3248_ = v___x_3283_;
goto v___jp_3247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(v_x_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_object* v_00_u03b1_3293_, lean_object* v_x_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_apply_1(v_x_3294_, lean_box(0));
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0___boxed(lean_object* v_00_u03b1_3302_, lean_object* v_x_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(v_00_u03b1_3302_, v_x_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0(lean_object* v_fvars_3312_, lean_object* v_pre_3313_, lean_object* v_post_3314_, uint8_t v_usedLetOnly_3315_, uint8_t v_skipConstInApp_3316_, uint8_t v_skipInstances_3317_, lean_object* v_body_3318_, lean_object* v_x_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_array_push(v_fvars_3312_, v_x_3319_);
v___x_3327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(v_pre_3313_, v_post_3314_, v_usedLetOnly_3315_, v_skipConstInApp_3316_, v_skipInstances_3317_, v___x_3326_, v_body_3318_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_3328_, lean_object* v_pre_3329_, lean_object* v_post_3330_, lean_object* v_usedLetOnly_3331_, lean_object* v_skipConstInApp_3332_, lean_object* v_skipInstances_3333_, lean_object* v_body_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
uint8_t v_usedLetOnly_boxed_3342_; uint8_t v_skipConstInApp_boxed_3343_; uint8_t v_skipInstances_boxed_3344_; lean_object* v_res_3345_; 
v_usedLetOnly_boxed_3342_ = lean_unbox(v_usedLetOnly_3331_);
v_skipConstInApp_boxed_3343_ = lean_unbox(v_skipConstInApp_3332_);
v_skipInstances_boxed_3344_ = lean_unbox(v_skipInstances_3333_);
v_res_3345_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0(v_fvars_3328_, v_pre_3329_, v_post_3330_, v_usedLetOnly_boxed_3342_, v_skipConstInApp_boxed_3343_, v_skipInstances_boxed_3344_, v_body_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(lean_object* v_pre_3346_, lean_object* v_post_3347_, uint8_t v_usedLetOnly_3348_, uint8_t v_skipConstInApp_3349_, uint8_t v_skipInstances_3350_, lean_object* v_e_3351_, lean_object* v_a_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; 
lean_inc_ref(v_post_3347_);
lean_inc(v___y_3356_);
lean_inc_ref(v___y_3355_);
lean_inc(v___y_3354_);
lean_inc_ref(v___y_3353_);
lean_inc_ref(v_e_3351_);
v___x_3358_ = lean_apply_6(v_post_3347_, v_e_3351_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, lean_box(0));
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3377_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3361_ = v___x_3358_;
v_isShared_3362_ = v_isSharedCheck_3377_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3377_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
switch(lean_obj_tag(v_a_3359_))
{
case 0:
{
lean_object* v_e_3363_; lean_object* v___x_3365_; 
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_e_3351_);
lean_dec_ref(v_post_3347_);
lean_dec_ref(v_pre_3346_);
v_e_3363_ = lean_ctor_get(v_a_3359_, 0);
lean_inc_ref(v_e_3363_);
lean_dec_ref(v_a_3359_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v_e_3363_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_e_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
case 1:
{
lean_object* v_e_3367_; lean_object* v___x_3368_; 
lean_del_object(v___x_3361_);
lean_dec_ref(v_e_3351_);
v_e_3367_ = lean_ctor_get(v_a_3359_, 0);
lean_inc_ref(v_e_3367_);
lean_dec_ref(v_a_3359_);
v___x_3368_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3346_, v_post_3347_, v_usedLetOnly_3348_, v_skipConstInApp_3349_, v_skipInstances_3350_, v_e_3367_, v_a_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
return v___x_3368_;
}
default: 
{
lean_object* v_e_x3f_3369_; 
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_post_3347_);
lean_dec_ref(v_pre_3346_);
v_e_x3f_3369_ = lean_ctor_get(v_a_3359_, 0);
lean_inc(v_e_x3f_3369_);
lean_dec_ref(v_a_3359_);
if (lean_obj_tag(v_e_x3f_3369_) == 0)
{
lean_object* v___x_3371_; 
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v_e_3351_);
v___x_3371_ = v___x_3361_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_e_3351_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; 
lean_dec_ref(v_e_3351_);
v_val_3373_ = lean_ctor_get(v_e_x3f_3369_, 0);
lean_inc(v_val_3373_);
lean_dec_ref(v_e_x3f_3369_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v_val_3373_);
v___x_3375_ = v___x_3361_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_val_3373_);
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
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_e_3351_);
lean_dec_ref(v_post_3347_);
lean_dec_ref(v_pre_3346_);
v_a_3378_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3358_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3358_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(lean_object* v_pre_3386_, lean_object* v_post_3387_, uint8_t v_usedLetOnly_3388_, uint8_t v_skipConstInApp_3389_, uint8_t v_skipInstances_3390_, lean_object* v_fvars_3391_, lean_object* v_e_3392_, lean_object* v_a_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
if (lean_obj_tag(v_e_3392_) == 6)
{
lean_object* v_binderName_3399_; lean_object* v_binderType_3400_; lean_object* v_body_3401_; uint8_t v_binderInfo_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_binderName_3399_ = lean_ctor_get(v_e_3392_, 0);
lean_inc(v_binderName_3399_);
v_binderType_3400_ = lean_ctor_get(v_e_3392_, 1);
lean_inc_ref(v_binderType_3400_);
v_body_3401_ = lean_ctor_get(v_e_3392_, 2);
lean_inc_ref(v_body_3401_);
v_binderInfo_3402_ = lean_ctor_get_uint8(v_e_3392_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3392_);
v___x_3403_ = lean_expr_instantiate_rev(v_binderType_3400_, v_fvars_3391_);
lean_dec_ref(v_binderType_3400_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc(v___y_3395_);
lean_inc_ref(v___y_3394_);
lean_inc(v_a_3393_);
lean_inc_ref(v_post_3387_);
lean_inc_ref(v_pre_3386_);
v___x_3404_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3386_, v_post_3387_, v_usedLetOnly_3388_, v_skipConstInApp_3389_, v_skipInstances_3390_, v___x_3403_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___f_3409_; uint8_t v___x_3410_; lean_object* v___x_3411_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v___x_3404_);
v___x_3406_ = lean_box(v_usedLetOnly_3388_);
v___x_3407_ = lean_box(v_skipConstInApp_3389_);
v___x_3408_ = lean_box(v_skipInstances_3390_);
v___f_3409_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3409_, 0, v_fvars_3391_);
lean_closure_set(v___f_3409_, 1, v_pre_3386_);
lean_closure_set(v___f_3409_, 2, v_post_3387_);
lean_closure_set(v___f_3409_, 3, v___x_3406_);
lean_closure_set(v___f_3409_, 4, v___x_3407_);
lean_closure_set(v___f_3409_, 5, v___x_3408_);
lean_closure_set(v___f_3409_, 6, v_body_3401_);
v___x_3410_ = 0;
v___x_3411_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_binderName_3399_, v_binderInfo_3402_, v_a_3405_, v___f_3409_, v___x_3410_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3411_;
}
else
{
lean_dec_ref(v_body_3401_);
lean_dec(v_binderName_3399_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_fvars_3391_);
lean_dec_ref(v_post_3387_);
lean_dec_ref(v_pre_3386_);
return v___x_3404_;
}
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_expr_instantiate_rev(v_e_3392_, v_fvars_3391_);
lean_dec_ref(v_e_3392_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc(v___y_3395_);
lean_inc_ref(v___y_3394_);
lean_inc(v_a_3393_);
lean_inc_ref(v_post_3387_);
lean_inc_ref(v_pre_3386_);
v___x_3413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3386_, v_post_3387_, v_usedLetOnly_3388_, v_skipConstInApp_3389_, v_skipInstances_3390_, v___x_3412_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; uint8_t v___x_3415_; uint8_t v___x_3416_; uint8_t v___x_3417_; lean_object* v___x_3418_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = 0;
v___x_3416_ = 1;
v___x_3417_ = 1;
v___x_3418_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3391_, v_a_3414_, v___x_3415_, v_usedLetOnly_3388_, v___x_3415_, v___x_3416_, v___x_3417_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec_ref(v_fvars_3391_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref(v___x_3418_);
v___x_3420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3386_, v_post_3387_, v_usedLetOnly_3388_, v_skipConstInApp_3389_, v_skipInstances_3390_, v_a_3419_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3420_;
}
else
{
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_post_3387_);
lean_dec_ref(v_pre_3386_);
return v___x_3418_;
}
}
else
{
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_fvars_3391_);
lean_dec_ref(v_post_3387_);
lean_dec_ref(v_pre_3386_);
return v___x_3413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0(lean_object* v_fvars_3421_, lean_object* v_pre_3422_, lean_object* v_post_3423_, uint8_t v_usedLetOnly_3424_, uint8_t v_skipConstInApp_3425_, uint8_t v_skipInstances_3426_, lean_object* v_body_3427_, lean_object* v_x_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_array_push(v_fvars_3421_, v_x_3428_);
v___x_3436_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(v_pre_3422_, v_post_3423_, v_usedLetOnly_3424_, v_skipConstInApp_3425_, v_skipInstances_3426_, v___x_3435_, v_body_3427_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_3437_, lean_object* v_pre_3438_, lean_object* v_post_3439_, lean_object* v_usedLetOnly_3440_, lean_object* v_skipConstInApp_3441_, lean_object* v_skipInstances_3442_, lean_object* v_body_3443_, lean_object* v_x_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
uint8_t v_usedLetOnly_boxed_3451_; uint8_t v_skipConstInApp_boxed_3452_; uint8_t v_skipInstances_boxed_3453_; lean_object* v_res_3454_; 
v_usedLetOnly_boxed_3451_ = lean_unbox(v_usedLetOnly_3440_);
v_skipConstInApp_boxed_3452_ = lean_unbox(v_skipConstInApp_3441_);
v_skipInstances_boxed_3453_ = lean_unbox(v_skipInstances_3442_);
v_res_3454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0(v_fvars_3437_, v_pre_3438_, v_post_3439_, v_usedLetOnly_boxed_3451_, v_skipConstInApp_boxed_3452_, v_skipInstances_boxed_3453_, v_body_3443_, v_x_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(lean_object* v_pre_3455_, lean_object* v_post_3456_, uint8_t v_usedLetOnly_3457_, uint8_t v_skipConstInApp_3458_, uint8_t v_skipInstances_3459_, lean_object* v_fvars_3460_, lean_object* v_e_3461_, lean_object* v_a_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
if (lean_obj_tag(v_e_3461_) == 8)
{
lean_object* v_declName_3468_; lean_object* v_type_3469_; lean_object* v_value_3470_; lean_object* v_body_3471_; uint8_t v_nondep_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_declName_3468_ = lean_ctor_get(v_e_3461_, 0);
lean_inc(v_declName_3468_);
v_type_3469_ = lean_ctor_get(v_e_3461_, 1);
lean_inc_ref(v_type_3469_);
v_value_3470_ = lean_ctor_get(v_e_3461_, 2);
lean_inc_ref(v_value_3470_);
v_body_3471_ = lean_ctor_get(v_e_3461_, 3);
lean_inc_ref(v_body_3471_);
v_nondep_3472_ = lean_ctor_get_uint8(v_e_3461_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3461_);
v___x_3473_ = lean_expr_instantiate_rev(v_type_3469_, v_fvars_3460_);
lean_dec_ref(v_type_3469_);
lean_inc(v___y_3466_);
lean_inc_ref(v___y_3465_);
lean_inc(v___y_3464_);
lean_inc_ref(v___y_3463_);
lean_inc(v_a_3462_);
lean_inc_ref(v_post_3456_);
lean_inc_ref(v_pre_3455_);
v___x_3474_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3455_, v_post_3456_, v_usedLetOnly_3457_, v_skipConstInApp_3458_, v_skipInstances_3459_, v___x_3473_, v_a_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = lean_expr_instantiate_rev(v_value_3470_, v_fvars_3460_);
lean_dec_ref(v_value_3470_);
lean_inc(v___y_3466_);
lean_inc_ref(v___y_3465_);
lean_inc(v___y_3464_);
lean_inc_ref(v___y_3463_);
lean_inc(v_a_3462_);
lean_inc_ref(v_post_3456_);
lean_inc_ref(v_pre_3455_);
v___x_3477_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3455_, v_post_3456_, v_usedLetOnly_3457_, v_skipConstInApp_3458_, v_skipInstances_3459_, v___x_3476_, v_a_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___f_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = lean_box(v_usedLetOnly_3457_);
v___x_3480_ = lean_box(v_skipConstInApp_3458_);
v___x_3481_ = lean_box(v_skipInstances_3459_);
v___f_3482_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3482_, 0, v_fvars_3460_);
lean_closure_set(v___f_3482_, 1, v_pre_3455_);
lean_closure_set(v___f_3482_, 2, v_post_3456_);
lean_closure_set(v___f_3482_, 3, v___x_3479_);
lean_closure_set(v___f_3482_, 4, v___x_3480_);
lean_closure_set(v___f_3482_, 5, v___x_3481_);
lean_closure_set(v___f_3482_, 6, v_body_3471_);
v___x_3483_ = 0;
v___x_3484_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(v_declName_3468_, v_a_3475_, v_a_3478_, v___f_3482_, v_nondep_3472_, v___x_3483_, v_a_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v___x_3484_;
}
else
{
lean_dec(v_a_3475_);
lean_dec_ref(v_body_3471_);
lean_dec(v_declName_3468_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_fvars_3460_);
lean_dec_ref(v_post_3456_);
lean_dec_ref(v_pre_3455_);
return v___x_3477_;
}
}
else
{
lean_dec_ref(v_body_3471_);
lean_dec_ref(v_value_3470_);
lean_dec(v_declName_3468_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_fvars_3460_);
lean_dec_ref(v_post_3456_);
lean_dec_ref(v_pre_3455_);
return v___x_3474_;
}
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_expr_instantiate_rev(v_e_3461_, v_fvars_3460_);
lean_dec_ref(v_e_3461_);
lean_inc(v___y_3466_);
lean_inc_ref(v___y_3465_);
lean_inc(v___y_3464_);
lean_inc_ref(v___y_3463_);
lean_inc(v_a_3462_);
lean_inc_ref(v_post_3456_);
lean_inc_ref(v_pre_3455_);
v___x_3486_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3455_, v_post_3456_, v_usedLetOnly_3457_, v_skipConstInApp_3458_, v_skipInstances_3459_, v___x_3485_, v_a_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; uint8_t v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref(v___x_3486_);
v___x_3488_ = 0;
v___x_3489_ = 1;
v___x_3490_ = l_Lean_Meta_mkLetFVars(v_fvars_3460_, v_a_3487_, v_usedLetOnly_3457_, v___x_3488_, v___x_3489_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec_ref(v_fvars_3460_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3492_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref(v___x_3490_);
v___x_3492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3455_, v_post_3456_, v_usedLetOnly_3457_, v_skipConstInApp_3458_, v_skipInstances_3459_, v_a_3491_, v_a_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v___x_3492_;
}
else
{
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_post_3456_);
lean_dec_ref(v_pre_3455_);
return v___x_3490_;
}
}
else
{
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_fvars_3460_);
lean_dec_ref(v_post_3456_);
lean_dec_ref(v_pre_3455_);
return v___x_3486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4(lean_object* v_pre_3493_, lean_object* v_post_3494_, uint8_t v_usedLetOnly_3495_, uint8_t v_skipConstInApp_3496_, uint8_t v_skipInstances_3497_, size_t v_sz_3498_, size_t v_i_3499_, lean_object* v_bs_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_usize_dec_lt(v_i_3499_, v_sz_3498_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v_post_3494_);
lean_dec_ref(v_pre_3493_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_bs_3500_);
return v___x_3508_;
}
else
{
lean_object* v_v_3509_; lean_object* v___x_3510_; 
v_v_3509_ = lean_array_uget_borrowed(v_bs_3500_, v_i_3499_);
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
lean_inc(v___y_3503_);
lean_inc_ref(v___y_3502_);
lean_inc(v___y_3501_);
lean_inc(v_v_3509_);
lean_inc_ref(v_post_3494_);
lean_inc_ref(v_pre_3493_);
v___x_3510_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3493_, v_post_3494_, v_usedLetOnly_3495_, v_skipConstInApp_3496_, v_skipInstances_3497_, v_v_3509_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v_bs_x27_3513_; size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref(v___x_3510_);
v___x_3512_ = lean_unsigned_to_nat(0u);
v_bs_x27_3513_ = lean_array_uset(v_bs_3500_, v_i_3499_, v___x_3512_);
v___x_3514_ = ((size_t)1ULL);
v___x_3515_ = lean_usize_add(v_i_3499_, v___x_3514_);
v___x_3516_ = lean_array_uset(v_bs_x27_3513_, v_i_3499_, v_a_3511_);
v_i_3499_ = v___x_3515_;
v_bs_3500_ = v___x_3516_;
goto _start;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v_bs_3500_);
lean_dec_ref(v_post_3494_);
lean_dec_ref(v_pre_3493_);
v_a_3518_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3510_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3510_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_3526_, lean_object* v_post_3527_, uint8_t v_usedLetOnly_3528_, uint8_t v_skipConstInApp_3529_, uint8_t v_skipInstances_3530_, lean_object* v___x_3531_, lean_object* v___y_3532_, lean_object* v_b_3533_, lean_object* v_a_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3526_, v_post_3527_, v_usedLetOnly_3528_, v_skipConstInApp_3529_, v_skipInstances_3530_, v___x_3531_, v___y_3532_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3550_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3543_ = v___x_3540_;
v_isShared_3544_ = v_isSharedCheck_3550_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3540_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3550_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3545_ = lean_array_fset(v_b_3533_, v_a_3534_, v_a_3541_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 0, v___x_3546_);
v___x_3548_ = v___x_3543_;
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
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_b_3533_);
v_a_3551_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3540_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3540_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_3559_, lean_object* v_post_3560_, lean_object* v_usedLetOnly_3561_, lean_object* v_skipConstInApp_3562_, lean_object* v_skipInstances_3563_, lean_object* v___x_3564_, lean_object* v___y_3565_, lean_object* v_b_3566_, lean_object* v_a_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v_usedLetOnly_boxed_3573_; uint8_t v_skipConstInApp_boxed_3574_; uint8_t v_skipInstances_boxed_3575_; lean_object* v_res_3576_; 
v_usedLetOnly_boxed_3573_ = lean_unbox(v_usedLetOnly_3561_);
v_skipConstInApp_boxed_3574_ = lean_unbox(v_skipConstInApp_3562_);
v_skipInstances_boxed_3575_ = lean_unbox(v_skipInstances_3563_);
v_res_3576_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0(v_pre_3559_, v_post_3560_, v_usedLetOnly_boxed_3573_, v_skipConstInApp_boxed_3574_, v_skipInstances_boxed_3575_, v___x_3564_, v___y_3565_, v_b_3566_, v_a_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec(v_a_3567_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(lean_object* v_upperBound_3577_, lean_object* v___x_3578_, lean_object* v_pre_3579_, lean_object* v_post_3580_, uint8_t v_usedLetOnly_3581_, uint8_t v_skipConstInApp_3582_, uint8_t v_skipInstances_3583_, lean_object* v_a_3584_, lean_object* v_b_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___y_3593_; uint8_t v___x_3616_; 
v___x_3616_ = lean_nat_dec_lt(v_a_3584_, v_upperBound_3577_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec(v_a_3584_);
lean_dec_ref(v_post_3580_);
lean_dec_ref(v_pre_3579_);
v___x_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3617_, 0, v_b_3585_);
return v___x_3617_;
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3618_ = lean_array_fget_borrowed(v_b_3585_, v_a_3584_);
v___x_3619_ = lean_array_get_size(v___x_3578_);
v___x_3620_ = lean_nat_dec_lt(v_a_3584_, v___x_3619_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___f_3624_; 
lean_inc(v___x_3618_);
v___x_3621_ = lean_box(v_usedLetOnly_3581_);
v___x_3622_ = lean_box(v_skipConstInApp_3582_);
v___x_3623_ = lean_box(v_skipInstances_3583_);
lean_inc(v_a_3584_);
lean_inc(v___y_3586_);
lean_inc_ref(v_post_3580_);
lean_inc_ref(v_pre_3579_);
v___f_3624_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3624_, 0, v_pre_3579_);
lean_closure_set(v___f_3624_, 1, v_post_3580_);
lean_closure_set(v___f_3624_, 2, v___x_3621_);
lean_closure_set(v___f_3624_, 3, v___x_3622_);
lean_closure_set(v___f_3624_, 4, v___x_3623_);
lean_closure_set(v___f_3624_, 5, v___x_3618_);
lean_closure_set(v___f_3624_, 6, v___y_3586_);
lean_closure_set(v___f_3624_, 7, v_b_3585_);
lean_closure_set(v___f_3624_, 8, v_a_3584_);
v___y_3593_ = v___f_3624_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3625_; uint8_t v_isInstance_3626_; 
v___x_3625_ = lean_array_fget_borrowed(v___x_3578_, v_a_3584_);
v_isInstance_3626_ = lean_ctor_get_uint8(v___x_3625_, sizeof(void*)*1 + 4);
if (v_isInstance_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___f_3630_; 
lean_inc(v___x_3618_);
v___x_3627_ = lean_box(v_usedLetOnly_3581_);
v___x_3628_ = lean_box(v_skipConstInApp_3582_);
v___x_3629_ = lean_box(v_skipInstances_3583_);
lean_inc(v_a_3584_);
lean_inc(v___y_3586_);
lean_inc_ref(v_post_3580_);
lean_inc_ref(v_pre_3579_);
v___f_3630_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3630_, 0, v_pre_3579_);
lean_closure_set(v___f_3630_, 1, v_post_3580_);
lean_closure_set(v___f_3630_, 2, v___x_3627_);
lean_closure_set(v___f_3630_, 3, v___x_3628_);
lean_closure_set(v___f_3630_, 4, v___x_3629_);
lean_closure_set(v___f_3630_, 5, v___x_3618_);
lean_closure_set(v___f_3630_, 6, v___y_3586_);
lean_closure_set(v___f_3630_, 7, v_b_3585_);
lean_closure_set(v___f_3630_, 8, v_a_3584_);
v___y_3593_ = v___f_3630_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3631_; lean_object* v___f_3632_; 
v___x_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3631_, 0, v_b_3585_);
v___f_3632_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3632_, 0, v___x_3631_);
v___y_3593_ = v___f_3632_;
goto v___jp_3592_;
}
}
}
v___jp_3592_:
{
lean_object* v___x_3594_; 
lean_inc(v___y_3590_);
lean_inc_ref(v___y_3589_);
lean_inc(v___y_3588_);
lean_inc_ref(v___y_3587_);
v___x_3594_ = lean_apply_5(v___y_3593_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, lean_box(0));
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3607_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3607_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3607_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
if (lean_obj_tag(v_a_3595_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; 
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec(v_a_3584_);
lean_dec_ref(v_post_3580_);
lean_dec_ref(v_pre_3579_);
v_a_3599_ = lean_ctor_get(v_a_3595_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v_a_3595_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v_a_3599_);
v___x_3601_ = v___x_3597_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
lean_del_object(v___x_3597_);
v_a_3603_ = lean_ctor_get(v_a_3595_, 0);
lean_inc(v_a_3603_);
lean_dec_ref(v_a_3595_);
v___x_3604_ = lean_unsigned_to_nat(1u);
v___x_3605_ = lean_nat_add(v_a_3584_, v___x_3604_);
lean_dec(v_a_3584_);
v_a_3584_ = v___x_3605_;
v_b_3585_ = v_a_3603_;
goto _start;
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec(v_a_3584_);
lean_dec_ref(v_post_3580_);
lean_dec_ref(v_pre_3579_);
v_a_3608_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3594_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3594_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10(uint8_t v_skipInstances_3633_, lean_object* v_pre_3634_, lean_object* v_post_3635_, uint8_t v_usedLetOnly_3636_, uint8_t v_skipConstInApp_3637_, lean_object* v_x_3638_, lean_object* v_x_3639_, lean_object* v_x_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_f_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; 
if (lean_obj_tag(v_x_3638_) == 5)
{
lean_object* v_fn_3696_; lean_object* v_arg_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_fn_3696_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_fn_3696_);
v_arg_3697_ = lean_ctor_get(v_x_3638_, 1);
lean_inc_ref(v_arg_3697_);
lean_dec_ref(v_x_3638_);
v___x_3698_ = lean_array_set(v_x_3639_, v_x_3640_, v_arg_3697_);
v___x_3699_ = lean_unsigned_to_nat(1u);
v___x_3700_ = lean_nat_sub(v_x_3640_, v___x_3699_);
lean_dec(v_x_3640_);
v_x_3638_ = v_fn_3696_;
v_x_3639_ = v___x_3698_;
v_x_3640_ = v___x_3700_;
goto _start;
}
else
{
lean_dec(v_x_3640_);
if (v_skipConstInApp_3637_ == 0)
{
goto v___jp_3693_;
}
else
{
uint8_t v___x_3702_; 
v___x_3702_ = l_Lean_Expr_isConst(v_x_3638_);
if (v___x_3702_ == 0)
{
goto v___jp_3693_;
}
else
{
v_f_3648_ = v_x_3638_;
v___y_3649_ = v___y_3641_;
v___y_3650_ = v___y_3642_;
v___y_3651_ = v___y_3643_;
v___y_3652_ = v___y_3644_;
v___y_3653_ = v___y_3645_;
goto v___jp_3647_;
}
}
}
v___jp_3647_:
{
if (v_skipInstances_3633_ == 0)
{
size_t v_sz_3654_; size_t v___x_3655_; lean_object* v___x_3656_; 
v_sz_3654_ = lean_array_size(v_x_3639_);
v___x_3655_ = ((size_t)0ULL);
lean_inc(v___y_3653_);
lean_inc_ref(v___y_3652_);
lean_inc(v___y_3651_);
lean_inc_ref(v___y_3650_);
lean_inc(v___y_3649_);
lean_inc_ref(v_post_3635_);
lean_inc_ref(v_pre_3634_);
v___x_3656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4(v_pre_3634_, v_post_3635_, v_usedLetOnly_3636_, v_skipConstInApp_3637_, v_skipInstances_3633_, v_sz_3654_, v___x_3655_, v_x_3639_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
v___x_3658_ = l_Lean_mkAppN(v_f_3648_, v_a_3657_);
lean_dec(v_a_3657_);
v___x_3659_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3634_, v_post_3635_, v_usedLetOnly_3636_, v_skipConstInApp_3637_, v_skipInstances_3633_, v___x_3658_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3659_;
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v_f_3648_);
lean_dec_ref(v_post_3635_);
lean_dec_ref(v_pre_3634_);
v_a_3660_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3656_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3656_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_array_get_size(v_x_3639_);
lean_inc(v___y_3653_);
lean_inc_ref(v___y_3652_);
lean_inc(v___y_3651_);
lean_inc_ref(v___y_3650_);
lean_inc_ref(v_f_3648_);
v___x_3669_ = l_Lean_Meta_getFunInfoNArgs(v_f_3648_, v___x_3668_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v_paramInfo_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v_paramInfo_3671_ = lean_ctor_get(v_a_3670_, 0);
lean_inc_ref(v_paramInfo_3671_);
lean_dec(v_a_3670_);
v___x_3672_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_3653_);
lean_inc_ref(v___y_3652_);
lean_inc(v___y_3651_);
lean_inc_ref(v___y_3650_);
lean_inc(v___y_3649_);
lean_inc_ref(v_post_3635_);
lean_inc_ref(v_pre_3634_);
v___x_3673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(v___x_3668_, v_paramInfo_3671_, v_pre_3634_, v_post_3635_, v_usedLetOnly_3636_, v_skipConstInApp_3637_, v_skipInstances_3633_, v___x_3672_, v_x_3639_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec_ref(v_paramInfo_3671_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___x_3675_ = l_Lean_mkAppN(v_f_3648_, v_a_3674_);
lean_dec(v_a_3674_);
v___x_3676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3634_, v_post_3635_, v_usedLetOnly_3636_, v_skipConstInApp_3637_, v_skipInstances_3633_, v___x_3675_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3676_;
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v_f_3648_);
lean_dec_ref(v_post_3635_);
lean_dec_ref(v_pre_3634_);
v_a_3677_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3673_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3673_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v_f_3648_);
lean_dec_ref(v_x_3639_);
lean_dec_ref(v_post_3635_);
lean_dec_ref(v_pre_3634_);
v_a_3685_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3669_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3669_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
v___jp_3693_:
{
lean_object* v___x_3694_; 
lean_inc(v___y_3645_);
lean_inc_ref(v___y_3644_);
lean_inc(v___y_3643_);
lean_inc_ref(v___y_3642_);
lean_inc(v___y_3641_);
lean_inc_ref(v_post_3635_);
lean_inc_ref(v_pre_3634_);
v___x_3694_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3634_, v_post_3635_, v_usedLetOnly_3636_, v_skipConstInApp_3637_, v_skipInstances_3633_, v_x_3638_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3694_);
v_f_3648_ = v_a_3695_;
v___y_3649_ = v___y_3641_;
v___y_3650_ = v___y_3642_;
v___y_3651_ = v___y_3643_;
v___y_3652_ = v___y_3644_;
v___y_3653_ = v___y_3645_;
goto v___jp_3647_;
}
else
{
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v_x_3639_);
lean_dec_ref(v_post_3635_);
lean_dec_ref(v_pre_3634_);
return v___x_3694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1(lean_object* v_pre_3703_, lean_object* v_e_3704_, lean_object* v_post_3705_, uint8_t v_usedLetOnly_3706_, uint8_t v_skipConstInApp_3707_, uint8_t v_skipInstances_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
lean_inc_ref(v_pre_3703_);
lean_inc(v___y_3713_);
lean_inc_ref(v___y_3712_);
lean_inc(v___y_3711_);
lean_inc_ref(v___y_3710_);
lean_inc_ref(v_e_3704_);
v___x_3715_ = lean_apply_6(v_pre_3703_, v_e_3704_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, lean_box(0));
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3764_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3718_ = v___x_3715_;
v_isShared_3719_ = v_isSharedCheck_3764_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3764_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___y_3721_; 
switch(lean_obj_tag(v_a_3716_))
{
case 0:
{
lean_object* v_e_3756_; lean_object* v___x_3758_; 
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v_post_3705_);
lean_dec_ref(v_e_3704_);
lean_dec_ref(v_pre_3703_);
v_e_3756_ = lean_ctor_get(v_a_3716_, 0);
lean_inc_ref(v_e_3756_);
lean_dec_ref(v_a_3716_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v_e_3756_);
v___x_3758_ = v___x_3718_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_e_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
case 1:
{
lean_object* v_e_3760_; lean_object* v___x_3761_; 
lean_del_object(v___x_3718_);
lean_dec_ref(v_e_3704_);
v_e_3760_ = lean_ctor_get(v_a_3716_, 0);
lean_inc_ref(v_e_3760_);
lean_dec_ref(v_a_3716_);
v___x_3761_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v_e_3760_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3761_;
}
default: 
{
lean_object* v_e_x3f_3762_; 
lean_del_object(v___x_3718_);
v_e_x3f_3762_ = lean_ctor_get(v_a_3716_, 0);
lean_inc(v_e_x3f_3762_);
lean_dec_ref(v_a_3716_);
if (lean_obj_tag(v_e_x3f_3762_) == 0)
{
v___y_3721_ = v_e_3704_;
goto v___jp_3720_;
}
else
{
lean_object* v_val_3763_; 
lean_dec_ref(v_e_3704_);
v_val_3763_ = lean_ctor_get(v_e_x3f_3762_, 0);
lean_inc(v_val_3763_);
lean_dec_ref(v_e_x3f_3762_);
v___y_3721_ = v_val_3763_;
goto v___jp_3720_;
}
}
}
v___jp_3720_:
{
switch(lean_obj_tag(v___y_3721_))
{
case 7:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0));
v___x_3723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___x_3722_, v___y_3721_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3723_;
}
case 6:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0));
v___x_3725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___x_3724_, v___y_3721_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3725_;
}
case 8:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0));
v___x_3727_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___x_3726_, v___y_3721_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3727_;
}
case 5:
{
lean_object* v_dummy_3728_; lean_object* v_nargs_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_dummy_3728_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3729_ = l_Lean_Expr_getAppNumArgs(v___y_3721_);
lean_inc(v_nargs_3729_);
v___x_3730_ = lean_mk_array(v_nargs_3729_, v_dummy_3728_);
v___x_3731_ = lean_unsigned_to_nat(1u);
v___x_3732_ = lean_nat_sub(v_nargs_3729_, v___x_3731_);
lean_dec(v_nargs_3729_);
v___x_3733_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10(v_skipInstances_3708_, v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v___y_3721_, v___x_3730_, v___x_3732_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3733_;
}
case 10:
{
lean_object* v_data_3734_; lean_object* v_expr_3735_; lean_object* v___x_3736_; 
v_data_3734_ = lean_ctor_get(v___y_3721_, 0);
v_expr_3735_ = lean_ctor_get(v___y_3721_, 1);
lean_inc(v___y_3713_);
lean_inc_ref(v___y_3712_);
lean_inc(v___y_3711_);
lean_inc_ref(v___y_3710_);
lean_inc(v___y_3709_);
lean_inc_ref(v_expr_3735_);
lean_inc_ref(v_post_3705_);
lean_inc_ref(v_pre_3703_);
v___x_3736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v_expr_3735_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; size_t v___x_3738_; size_t v___x_3739_; uint8_t v___x_3740_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref(v___x_3736_);
v___x_3738_ = lean_ptr_addr(v_expr_3735_);
v___x_3739_ = lean_ptr_addr(v_a_3737_);
v___x_3740_ = lean_usize_dec_eq(v___x_3738_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_inc(v_data_3734_);
lean_dec_ref(v___y_3721_);
v___x_3741_ = l_Lean_Expr_mdata___override(v_data_3734_, v_a_3737_);
v___x_3742_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___x_3741_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3742_;
}
else
{
lean_object* v___x_3743_; 
lean_dec(v_a_3737_);
v___x_3743_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___y_3721_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3743_;
}
}
else
{
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v_post_3705_);
lean_dec_ref(v_pre_3703_);
return v___x_3736_;
}
}
case 11:
{
lean_object* v_typeName_3744_; lean_object* v_idx_3745_; lean_object* v_struct_3746_; lean_object* v___x_3747_; 
v_typeName_3744_ = lean_ctor_get(v___y_3721_, 0);
v_idx_3745_ = lean_ctor_get(v___y_3721_, 1);
v_struct_3746_ = lean_ctor_get(v___y_3721_, 2);
lean_inc(v___y_3713_);
lean_inc_ref(v___y_3712_);
lean_inc(v___y_3711_);
lean_inc_ref(v___y_3710_);
lean_inc(v___y_3709_);
lean_inc_ref(v_struct_3746_);
lean_inc_ref(v_post_3705_);
lean_inc_ref(v_pre_3703_);
v___x_3747_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v_struct_3746_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; size_t v___x_3749_; size_t v___x_3750_; uint8_t v___x_3751_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
lean_dec_ref(v___x_3747_);
v___x_3749_ = lean_ptr_addr(v_struct_3746_);
v___x_3750_ = lean_ptr_addr(v_a_3748_);
v___x_3751_ = lean_usize_dec_eq(v___x_3749_, v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_inc(v_idx_3745_);
lean_inc(v_typeName_3744_);
lean_dec_ref(v___y_3721_);
v___x_3752_ = l_Lean_Expr_proj___override(v_typeName_3744_, v_idx_3745_, v_a_3748_);
v___x_3753_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___x_3752_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3753_;
}
else
{
lean_object* v___x_3754_; 
lean_dec(v_a_3748_);
v___x_3754_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___y_3721_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3754_;
}
}
else
{
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v_post_3705_);
lean_dec_ref(v_pre_3703_);
return v___x_3747_;
}
}
default: 
{
lean_object* v___x_3755_; 
v___x_3755_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3703_, v_post_3705_, v_usedLetOnly_3706_, v_skipConstInApp_3707_, v_skipInstances_3708_, v___y_3721_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3755_;
}
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v_post_3705_);
lean_dec_ref(v_e_3704_);
lean_dec_ref(v_pre_3703_);
v_a_3765_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3715_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3715_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___boxed(lean_object* v_pre_3773_, lean_object* v_e_3774_, lean_object* v_post_3775_, lean_object* v_usedLetOnly_3776_, lean_object* v_skipConstInApp_3777_, lean_object* v_skipInstances_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
uint8_t v_usedLetOnly_boxed_3785_; uint8_t v_skipConstInApp_boxed_3786_; uint8_t v_skipInstances_boxed_3787_; lean_object* v_res_3788_; 
v_usedLetOnly_boxed_3785_ = lean_unbox(v_usedLetOnly_3776_);
v_skipConstInApp_boxed_3786_ = lean_unbox(v_skipConstInApp_3777_);
v_skipInstances_boxed_3787_ = lean_unbox(v_skipInstances_3778_);
v_res_3788_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1(v_pre_3773_, v_e_3774_, v_post_3775_, v_usedLetOnly_boxed_3785_, v_skipConstInApp_boxed_3786_, v_skipInstances_boxed_3787_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(lean_object* v_pre_3789_, lean_object* v_post_3790_, uint8_t v_usedLetOnly_3791_, uint8_t v_skipConstInApp_3792_, uint8_t v_skipInstances_3793_, lean_object* v_e_3794_, lean_object* v_a_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_inc(v_a_3795_);
v___x_3801_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3801_, 0, lean_box(0));
lean_closure_set(v___x_3801_, 1, lean_box(0));
lean_closure_set(v___x_3801_, 2, v_a_3795_);
v___x_3802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___x_3801_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3836_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3836_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3836_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3803_, v_e_3794_);
lean_dec(v_a_3803_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___f_3811_; lean_object* v___x_3812_; 
lean_del_object(v___x_3805_);
v___x_3808_ = lean_box(v_usedLetOnly_3791_);
v___x_3809_ = lean_box(v_skipConstInApp_3792_);
v___x_3810_ = lean_box(v_skipInstances_3793_);
lean_inc_ref(v_e_3794_);
v___f_3811_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3811_, 0, v_pre_3789_);
lean_closure_set(v___f_3811_, 1, v_e_3794_);
lean_closure_set(v___f_3811_, 2, v_post_3790_);
lean_closure_set(v___f_3811_, 3, v___x_3808_);
lean_closure_set(v___f_3811_, 4, v___x_3809_);
lean_closure_set(v___f_3811_, 5, v___x_3810_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
lean_inc(v___y_3797_);
lean_inc_ref(v___y_3796_);
lean_inc(v_a_3795_);
v___x_3812_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(v___f_3811_, v_a_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___f_3814_; lean_object* v___x_3815_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3812_);
lean_inc(v_a_3813_);
v___f_3814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3814_, 0, v_a_3795_);
lean_closure_set(v___f_3814_, 1, v_e_3794_);
lean_closure_set(v___f_3814_, 2, v_a_3813_);
v___x_3815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___f_3814_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; 
v_unused_3823_ = lean_ctor_get(v___x_3815_, 0);
lean_dec(v_unused_3823_);
v___x_3817_ = v___x_3815_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v___x_3815_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v_a_3813_);
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3813_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_a_3813_);
v_a_3824_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3815_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3815_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_e_3794_);
return v___x_3812_;
}
}
else
{
lean_object* v_val_3832_; lean_object* v___x_3834_; 
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_e_3794_);
lean_dec_ref(v_post_3790_);
lean_dec_ref(v_pre_3789_);
v_val_3832_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_val_3832_);
lean_dec_ref(v___x_3807_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v_val_3832_);
v___x_3834_ = v___x_3805_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_val_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_e_3794_);
lean_dec_ref(v_post_3790_);
lean_dec_ref(v_pre_3789_);
v_a_3837_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3802_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3802_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_fvars_3845_, lean_object* v_pre_3846_, lean_object* v_post_3847_, lean_object* v_usedLetOnly_3848_, lean_object* v_skipConstInApp_3849_, lean_object* v_skipInstances_3850_, lean_object* v_body_3851_, lean_object* v_x_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
uint8_t v_usedLetOnly_boxed_3859_; uint8_t v_skipConstInApp_boxed_3860_; uint8_t v_skipInstances_boxed_3861_; lean_object* v_res_3862_; 
v_usedLetOnly_boxed_3859_ = lean_unbox(v_usedLetOnly_3848_);
v_skipConstInApp_boxed_3860_ = lean_unbox(v_skipConstInApp_3849_);
v_skipInstances_boxed_3861_ = lean_unbox(v_skipInstances_3850_);
v_res_3862_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0(v_fvars_3845_, v_pre_3846_, v_post_3847_, v_usedLetOnly_boxed_3859_, v_skipConstInApp_boxed_3860_, v_skipInstances_boxed_3861_, v_body_3851_, v_x_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(lean_object* v_pre_3863_, lean_object* v_post_3864_, uint8_t v_usedLetOnly_3865_, uint8_t v_skipConstInApp_3866_, uint8_t v_skipInstances_3867_, lean_object* v_fvars_3868_, lean_object* v_e_3869_, lean_object* v_a_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
if (lean_obj_tag(v_e_3869_) == 7)
{
lean_object* v_binderName_3876_; lean_object* v_binderType_3877_; lean_object* v_body_3878_; uint8_t v_binderInfo_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_binderName_3876_ = lean_ctor_get(v_e_3869_, 0);
lean_inc(v_binderName_3876_);
v_binderType_3877_ = lean_ctor_get(v_e_3869_, 1);
lean_inc_ref(v_binderType_3877_);
v_body_3878_ = lean_ctor_get(v_e_3869_, 2);
lean_inc_ref(v_body_3878_);
v_binderInfo_3879_ = lean_ctor_get_uint8(v_e_3869_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3869_);
v___x_3880_ = lean_expr_instantiate_rev(v_binderType_3877_, v_fvars_3868_);
lean_dec_ref(v_binderType_3877_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3873_);
lean_inc(v___y_3872_);
lean_inc_ref(v___y_3871_);
lean_inc(v_a_3870_);
lean_inc_ref(v_post_3864_);
lean_inc_ref(v_pre_3863_);
v___x_3881_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3863_, v_post_3864_, v_usedLetOnly_3865_, v_skipConstInApp_3866_, v_skipInstances_3867_, v___x_3880_, v_a_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___f_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref(v___x_3881_);
v___x_3883_ = lean_box(v_usedLetOnly_3865_);
v___x_3884_ = lean_box(v_skipConstInApp_3866_);
v___x_3885_ = lean_box(v_skipInstances_3867_);
v___f_3886_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3886_, 0, v_fvars_3868_);
lean_closure_set(v___f_3886_, 1, v_pre_3863_);
lean_closure_set(v___f_3886_, 2, v_post_3864_);
lean_closure_set(v___f_3886_, 3, v___x_3883_);
lean_closure_set(v___f_3886_, 4, v___x_3884_);
lean_closure_set(v___f_3886_, 5, v___x_3885_);
lean_closure_set(v___f_3886_, 6, v_body_3878_);
v___x_3887_ = 0;
v___x_3888_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_binderName_3876_, v_binderInfo_3879_, v_a_3882_, v___f_3886_, v___x_3887_, v_a_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3888_;
}
else
{
lean_dec_ref(v_body_3878_);
lean_dec(v_binderName_3876_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_fvars_3868_);
lean_dec_ref(v_post_3864_);
lean_dec_ref(v_pre_3863_);
return v___x_3881_;
}
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_expr_instantiate_rev(v_e_3869_, v_fvars_3868_);
lean_dec_ref(v_e_3869_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3873_);
lean_inc(v___y_3872_);
lean_inc_ref(v___y_3871_);
lean_inc(v_a_3870_);
lean_inc_ref(v_post_3864_);
lean_inc_ref(v_pre_3863_);
v___x_3890_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3863_, v_post_3864_, v_usedLetOnly_3865_, v_skipConstInApp_3866_, v_skipInstances_3867_, v___x_3889_, v_a_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; uint8_t v___x_3892_; uint8_t v___x_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref(v___x_3890_);
v___x_3892_ = 0;
v___x_3893_ = 1;
v___x_3894_ = 1;
v___x_3895_ = l_Lean_Meta_mkForallFVars(v_fvars_3868_, v_a_3891_, v___x_3892_, v_usedLetOnly_3865_, v___x_3893_, v___x_3894_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec_ref(v_fvars_3868_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
v___x_3897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3863_, v_post_3864_, v_usedLetOnly_3865_, v_skipConstInApp_3866_, v_skipInstances_3867_, v_a_3896_, v_a_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3897_;
}
else
{
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_post_3864_);
lean_dec_ref(v_pre_3863_);
return v___x_3895_;
}
}
else
{
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_fvars_3868_);
lean_dec_ref(v_post_3864_);
lean_dec_ref(v_pre_3863_);
return v___x_3890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0(lean_object* v_fvars_3898_, lean_object* v_pre_3899_, lean_object* v_post_3900_, uint8_t v_usedLetOnly_3901_, uint8_t v_skipConstInApp_3902_, uint8_t v_skipInstances_3903_, lean_object* v_body_3904_, lean_object* v_x_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = lean_array_push(v_fvars_3898_, v_x_3905_);
v___x_3913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(v_pre_3899_, v_post_3900_, v_usedLetOnly_3901_, v_skipConstInApp_3902_, v_skipInstances_3903_, v___x_3912_, v_body_3904_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5___boxed(lean_object* v_pre_3914_, lean_object* v_post_3915_, lean_object* v_usedLetOnly_3916_, lean_object* v_skipConstInApp_3917_, lean_object* v_skipInstances_3918_, lean_object* v_e_3919_, lean_object* v_a_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
uint8_t v_usedLetOnly_boxed_3926_; uint8_t v_skipConstInApp_boxed_3927_; uint8_t v_skipInstances_boxed_3928_; lean_object* v_res_3929_; 
v_usedLetOnly_boxed_3926_ = lean_unbox(v_usedLetOnly_3916_);
v_skipConstInApp_boxed_3927_ = lean_unbox(v_skipConstInApp_3917_);
v_skipInstances_boxed_3928_ = lean_unbox(v_skipInstances_3918_);
v_res_3929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3914_, v_post_3915_, v_usedLetOnly_boxed_3926_, v_skipConstInApp_boxed_3927_, v_skipInstances_boxed_3928_, v_e_3919_, v_a_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4___boxed(lean_object* v_pre_3930_, lean_object* v_post_3931_, lean_object* v_usedLetOnly_3932_, lean_object* v_skipConstInApp_3933_, lean_object* v_skipInstances_3934_, lean_object* v_sz_3935_, lean_object* v_i_3936_, lean_object* v_bs_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
uint8_t v_usedLetOnly_boxed_3944_; uint8_t v_skipConstInApp_boxed_3945_; uint8_t v_skipInstances_boxed_3946_; size_t v_sz_boxed_3947_; size_t v_i_boxed_3948_; lean_object* v_res_3949_; 
v_usedLetOnly_boxed_3944_ = lean_unbox(v_usedLetOnly_3932_);
v_skipConstInApp_boxed_3945_ = lean_unbox(v_skipConstInApp_3933_);
v_skipInstances_boxed_3946_ = lean_unbox(v_skipInstances_3934_);
v_sz_boxed_3947_ = lean_unbox_usize(v_sz_3935_);
lean_dec(v_sz_3935_);
v_i_boxed_3948_ = lean_unbox_usize(v_i_3936_);
lean_dec(v_i_3936_);
v_res_3949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4(v_pre_3930_, v_post_3931_, v_usedLetOnly_boxed_3944_, v_skipConstInApp_boxed_3945_, v_skipInstances_boxed_3946_, v_sz_boxed_3947_, v_i_boxed_3948_, v_bs_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___boxed(lean_object* v_pre_3950_, lean_object* v_post_3951_, lean_object* v_usedLetOnly_3952_, lean_object* v_skipConstInApp_3953_, lean_object* v_skipInstances_3954_, lean_object* v_e_3955_, lean_object* v_a_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
uint8_t v_usedLetOnly_boxed_3962_; uint8_t v_skipConstInApp_boxed_3963_; uint8_t v_skipInstances_boxed_3964_; lean_object* v_res_3965_; 
v_usedLetOnly_boxed_3962_ = lean_unbox(v_usedLetOnly_3952_);
v_skipConstInApp_boxed_3963_ = lean_unbox(v_skipConstInApp_3953_);
v_skipInstances_boxed_3964_ = lean_unbox(v_skipInstances_3954_);
v_res_3965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3950_, v_post_3951_, v_usedLetOnly_boxed_3962_, v_skipConstInApp_boxed_3963_, v_skipInstances_boxed_3964_, v_e_3955_, v_a_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___boxed(lean_object* v_pre_3966_, lean_object* v_post_3967_, lean_object* v_usedLetOnly_3968_, lean_object* v_skipConstInApp_3969_, lean_object* v_skipInstances_3970_, lean_object* v_fvars_3971_, lean_object* v_e_3972_, lean_object* v_a_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
uint8_t v_usedLetOnly_boxed_3979_; uint8_t v_skipConstInApp_boxed_3980_; uint8_t v_skipInstances_boxed_3981_; lean_object* v_res_3982_; 
v_usedLetOnly_boxed_3979_ = lean_unbox(v_usedLetOnly_3968_);
v_skipConstInApp_boxed_3980_ = lean_unbox(v_skipConstInApp_3969_);
v_skipInstances_boxed_3981_ = lean_unbox(v_skipInstances_3970_);
v_res_3982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(v_pre_3966_, v_post_3967_, v_usedLetOnly_boxed_3979_, v_skipConstInApp_boxed_3980_, v_skipInstances_boxed_3981_, v_fvars_3971_, v_e_3972_, v_a_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___boxed(lean_object* v_pre_3983_, lean_object* v_post_3984_, lean_object* v_usedLetOnly_3985_, lean_object* v_skipConstInApp_3986_, lean_object* v_skipInstances_3987_, lean_object* v_fvars_3988_, lean_object* v_e_3989_, lean_object* v_a_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
uint8_t v_usedLetOnly_boxed_3996_; uint8_t v_skipConstInApp_boxed_3997_; uint8_t v_skipInstances_boxed_3998_; lean_object* v_res_3999_; 
v_usedLetOnly_boxed_3996_ = lean_unbox(v_usedLetOnly_3985_);
v_skipConstInApp_boxed_3997_ = lean_unbox(v_skipConstInApp_3986_);
v_skipInstances_boxed_3998_ = lean_unbox(v_skipInstances_3987_);
v_res_3999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(v_pre_3983_, v_post_3984_, v_usedLetOnly_boxed_3996_, v_skipConstInApp_boxed_3997_, v_skipInstances_boxed_3998_, v_fvars_3988_, v_e_3989_, v_a_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___boxed(lean_object* v_pre_4000_, lean_object* v_post_4001_, lean_object* v_usedLetOnly_4002_, lean_object* v_skipConstInApp_4003_, lean_object* v_skipInstances_4004_, lean_object* v_fvars_4005_, lean_object* v_e_4006_, lean_object* v_a_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
uint8_t v_usedLetOnly_boxed_4013_; uint8_t v_skipConstInApp_boxed_4014_; uint8_t v_skipInstances_boxed_4015_; lean_object* v_res_4016_; 
v_usedLetOnly_boxed_4013_ = lean_unbox(v_usedLetOnly_4002_);
v_skipConstInApp_boxed_4014_ = lean_unbox(v_skipConstInApp_4003_);
v_skipInstances_boxed_4015_ = lean_unbox(v_skipInstances_4004_);
v_res_4016_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(v_pre_4000_, v_post_4001_, v_usedLetOnly_boxed_4013_, v_skipConstInApp_boxed_4014_, v_skipInstances_boxed_4015_, v_fvars_4005_, v_e_4006_, v_a_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_4017_, lean_object* v___x_4018_, lean_object* v_pre_4019_, lean_object* v_post_4020_, lean_object* v_usedLetOnly_4021_, lean_object* v_skipConstInApp_4022_, lean_object* v_skipInstances_4023_, lean_object* v_a_4024_, lean_object* v_b_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
uint8_t v_usedLetOnly_boxed_4032_; uint8_t v_skipConstInApp_boxed_4033_; uint8_t v_skipInstances_boxed_4034_; lean_object* v_res_4035_; 
v_usedLetOnly_boxed_4032_ = lean_unbox(v_usedLetOnly_4021_);
v_skipConstInApp_boxed_4033_ = lean_unbox(v_skipConstInApp_4022_);
v_skipInstances_boxed_4034_ = lean_unbox(v_skipInstances_4023_);
v_res_4035_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(v_upperBound_4017_, v___x_4018_, v_pre_4019_, v_post_4020_, v_usedLetOnly_boxed_4032_, v_skipConstInApp_boxed_4033_, v_skipInstances_boxed_4034_, v_a_4024_, v_b_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec_ref(v___x_4018_);
lean_dec(v_upperBound_4017_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10___boxed(lean_object* v_skipInstances_4036_, lean_object* v_pre_4037_, lean_object* v_post_4038_, lean_object* v_usedLetOnly_4039_, lean_object* v_skipConstInApp_4040_, lean_object* v_x_4041_, lean_object* v_x_4042_, lean_object* v_x_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
uint8_t v_skipInstances_boxed_4050_; uint8_t v_usedLetOnly_boxed_4051_; uint8_t v_skipConstInApp_boxed_4052_; lean_object* v_res_4053_; 
v_skipInstances_boxed_4050_ = lean_unbox(v_skipInstances_4036_);
v_usedLetOnly_boxed_4051_ = lean_unbox(v_usedLetOnly_4039_);
v_skipConstInApp_boxed_4052_ = lean_unbox(v_skipConstInApp_4040_);
v_res_4053_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10(v_skipInstances_boxed_4050_, v_pre_4037_, v_post_4038_, v_usedLetOnly_boxed_4051_, v_skipConstInApp_boxed_4052_, v_x_4041_, v_x_4042_, v_x_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2(lean_object* v_input_4054_, lean_object* v_pre_4055_, lean_object* v_post_4056_, uint8_t v_usedLetOnly_4057_, uint8_t v_skipConstInApp_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v_a_4066_; uint8_t v___x_4067_; lean_object* v___x_4068_; 
v___x_4064_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4065_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4064_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4066_);
lean_dec_ref(v___x_4065_);
v___x_4067_ = 0;
lean_inc(v___y_4062_);
lean_inc_ref(v___y_4061_);
lean_inc(v___y_4060_);
lean_inc_ref(v___y_4059_);
lean_inc(v_a_4066_);
v___x_4068_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_4055_, v_post_4056_, v_usedLetOnly_4057_, v_skipConstInApp_4058_, v___x_4067_, v_input_4054_, v_a_4066_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref(v___x_4068_);
v___x_4070_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4070_, 0, lean_box(0));
lean_closure_set(v___x_4070_, 1, lean_box(0));
lean_closure_set(v___x_4070_, 2, v_a_4066_);
v___x_4071_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4070_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; 
v_unused_4079_ = lean_ctor_get(v___x_4071_, 0);
lean_dec(v_unused_4079_);
v___x_4073_ = v___x_4071_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_dec(v___x_4071_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 0, v_a_4069_);
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4069_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
else
{
lean_dec(v_a_4066_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
return v___x_4068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___boxed(lean_object* v_input_4080_, lean_object* v_pre_4081_, lean_object* v_post_4082_, lean_object* v_usedLetOnly_4083_, lean_object* v_skipConstInApp_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
uint8_t v_usedLetOnly_boxed_4090_; uint8_t v_skipConstInApp_boxed_4091_; lean_object* v_res_4092_; 
v_usedLetOnly_boxed_4090_ = lean_unbox(v_usedLetOnly_4083_);
v_skipConstInApp_boxed_4091_ = lean_unbox(v_skipConstInApp_4084_);
v_res_4092_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2(v_input_4080_, v_pre_4081_, v_post_4082_, v_usedLetOnly_boxed_4090_, v_skipConstInApp_boxed_4091_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v___f_4102_; lean_object* v___x_4103_; 
v___f_4102_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__0));
v___x_4103_ = lean_find_expr(v___f_4102_, v_e_4096_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v___x_4104_; 
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_e_4096_);
return v___x_4104_;
}
else
{
lean_object* v_post_4105_; lean_object* v___f_4106_; uint8_t v___x_4107_; lean_object* v___x_4108_; 
lean_dec_ref(v___x_4103_);
v_post_4105_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__1));
v___f_4106_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__2));
v___x_4107_ = 0;
v___x_4108_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2(v_e_4096_, v___f_4106_, v_post_4105_, v___x_4107_, v___x_4107_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Meta_Grind_foldProjs(v_e_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6(lean_object* v_upperBound_4116_, lean_object* v___x_4117_, lean_object* v_pre_4118_, lean_object* v_post_4119_, uint8_t v_usedLetOnly_4120_, uint8_t v_skipConstInApp_4121_, uint8_t v_skipInstances_4122_, lean_object* v___x_4123_, lean_object* v_inst_4124_, lean_object* v_R_4125_, lean_object* v_a_4126_, lean_object* v_b_4127_, lean_object* v_c_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(v_upperBound_4116_, v___x_4117_, v_pre_4118_, v_post_4119_, v_usedLetOnly_4120_, v_skipConstInApp_4121_, v_skipInstances_4122_, v_a_4126_, v_b_4127_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_4136_ = _args[0];
lean_object* v___x_4137_ = _args[1];
lean_object* v_pre_4138_ = _args[2];
lean_object* v_post_4139_ = _args[3];
lean_object* v_usedLetOnly_4140_ = _args[4];
lean_object* v_skipConstInApp_4141_ = _args[5];
lean_object* v_skipInstances_4142_ = _args[6];
lean_object* v___x_4143_ = _args[7];
lean_object* v_inst_4144_ = _args[8];
lean_object* v_R_4145_ = _args[9];
lean_object* v_a_4146_ = _args[10];
lean_object* v_b_4147_ = _args[11];
lean_object* v_c_4148_ = _args[12];
lean_object* v___y_4149_ = _args[13];
lean_object* v___y_4150_ = _args[14];
lean_object* v___y_4151_ = _args[15];
lean_object* v___y_4152_ = _args[16];
lean_object* v___y_4153_ = _args[17];
lean_object* v___y_4154_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4155_; uint8_t v_skipConstInApp_boxed_4156_; uint8_t v_skipInstances_boxed_4157_; lean_object* v_res_4158_; 
v_usedLetOnly_boxed_4155_ = lean_unbox(v_usedLetOnly_4140_);
v_skipConstInApp_boxed_4156_ = lean_unbox(v_skipConstInApp_4141_);
v_skipInstances_boxed_4157_ = lean_unbox(v_skipInstances_4142_);
v_res_4158_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6(v_upperBound_4136_, v___x_4137_, v_pre_4138_, v_post_4139_, v_usedLetOnly_boxed_4155_, v_skipConstInApp_boxed_4156_, v_skipInstances_boxed_4157_, v___x_4143_, v_inst_4144_, v_R_4145_, v_a_4146_, v_b_4147_, v_c_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___x_4143_);
lean_dec_ref(v___x_4137_);
lean_dec(v_upperBound_4136_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_4159_, lean_object* v_name_4160_, uint8_t v_bi_4161_, lean_object* v_type_4162_, lean_object* v_k_4163_, uint8_t v_kind_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_name_4160_, v_bi_4161_, v_type_4162_, v_k_4163_, v_kind_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4172_, lean_object* v_name_4173_, lean_object* v_bi_4174_, lean_object* v_type_4175_, lean_object* v_k_4176_, lean_object* v_kind_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
uint8_t v_bi_boxed_4184_; uint8_t v_kind_boxed_4185_; lean_object* v_res_4186_; 
v_bi_boxed_4184_ = lean_unbox(v_bi_4174_);
v_kind_boxed_4185_ = lean_unbox(v_kind_4177_);
v_res_4186_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8(v_00_u03b1_4172_, v_name_4173_, v_bi_boxed_4184_, v_type_4175_, v_k_4176_, v_kind_boxed_4185_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_4187_, lean_object* v_name_4188_, lean_object* v_type_4189_, lean_object* v_val_4190_, lean_object* v_k_4191_, uint8_t v_nondep_4192_, uint8_t v_kind_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(v_name_4188_, v_type_4189_, v_val_4190_, v_k_4191_, v_nondep_4192_, v_kind_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4201_, lean_object* v_name_4202_, lean_object* v_type_4203_, lean_object* v_val_4204_, lean_object* v_k_4205_, lean_object* v_nondep_4206_, lean_object* v_kind_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v_nondep_boxed_4214_; uint8_t v_kind_boxed_4215_; lean_object* v_res_4216_; 
v_nondep_boxed_4214_ = lean_unbox(v_nondep_4206_);
v_kind_boxed_4215_ = lean_unbox(v_kind_4207_);
v_res_4216_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_4201_, v_name_4202_, v_type_4203_, v_val_4204_, v_k_4205_, v_nondep_boxed_4214_, v_kind_boxed_4215_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14(lean_object* v_00_u03b1_4217_, lean_object* v_ref_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(v_ref_4218_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___boxed(lean_object* v_00_u03b1_4225_, lean_object* v_ref_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14(v_00_u03b1_4225_, v_ref_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11(lean_object* v_00_u03b1_4233_, lean_object* v_x_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(v_x_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b1_4242_, lean_object* v_x_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11(v_00_u03b1_4242_, v_x_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_4258_, lean_object* v_config_4259_, lean_object* v_a_00___x40___internal___hyg_4260_, lean_object* v_a_00___x40___internal___hyg_4261_, lean_object* v_a_00___x40___internal___hyg_4262_, lean_object* v_a_00___x40___internal___hyg_4263_, lean_object* v_a_00___x40___internal___hyg_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = lean_grind_normalize(v_e_4258_, v_config_4259_, v_a_00___x40___internal___hyg_4260_, v_a_00___x40___internal___hyg_4261_, v_a_00___x40___internal___hyg_4262_, v_a_00___x40___internal___hyg_4263_);
return v_res_4265_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = lean_box(0);
v___x_4274_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4275_ = l_Lean_mkConst(v___x_4274_, v___x_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_4276_){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_4278_ = l_Lean_Expr_app___override(v___x_4277_, v_e_4276_);
return v___x_4278_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_4279_){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; uint8_t v___x_4282_; 
v___x_4280_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4281_ = lean_unsigned_to_nat(1u);
v___x_4282_ = l_Lean_Expr_isAppOfArity(v_e_4279_, v___x_4280_, v___x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_4283_){
_start:
{
uint8_t v_res_4284_; lean_object* v_r_4285_; 
v_res_4284_ = l_Lean_Meta_Grind_isMatchCond(v_e_4283_);
lean_dec_ref(v_e_4283_);
v_r_4285_ = lean_box(v_res_4284_);
return v_r_4285_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = lean_box(0);
v___x_4292_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4293_ = l_Lean_mkConst(v___x_4292_, v___x_4291_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_4294_){
_start:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_4296_ = l_Lean_Expr_app___override(v___x_4295_, v_e_4294_);
return v___x_4296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_4297_){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4298_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4299_ = lean_unsigned_to_nat(1u);
v___x_4300_ = l_Lean_Expr_isAppOfArity(v_e_4297_, v___x_4298_, v___x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_4301_){
_start:
{
uint8_t v_res_4302_; lean_object* v_r_4303_; 
v_res_4302_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_4301_);
lean_dec_ref(v_e_4301_);
v_r_4303_ = lean_box(v_res_4302_);
return v_r_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v___x_4307_; 
lean_inc_ref(v_e_4304_);
v___x_4307_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4304_, v_a_4305_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4324_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4324_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4324_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4317_ = l_Lean_Expr_cleanupAnnotations(v_a_4308_);
v___x_4318_ = l_Lean_Expr_isApp(v___x_4317_);
if (v___x_4318_ == 0)
{
lean_dec_ref(v___x_4317_);
lean_dec_ref(v_e_4304_);
goto v___jp_4312_;
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4320_; uint8_t v___x_4321_; 
v___x_4319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4317_);
v___x_4320_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4321_ = l_Lean_Expr_isConstOf(v___x_4319_, v___x_4320_);
lean_dec_ref(v___x_4319_);
if (v___x_4321_ == 0)
{
lean_dec_ref(v_e_4304_);
goto v___jp_4312_;
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
lean_del_object(v___x_4310_);
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v_e_4304_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
return v___x_4323_;
}
}
v___jp_4312_:
{
lean_object* v___x_4313_; lean_object* v___x_4315_; 
v___x_4313_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v___x_4313_);
v___x_4315_ = v___x_4310_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v_e_4304_);
v_a_4325_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4307_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4307_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4333_, v_a_4334_);
lean_dec(v_a_4334_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4337_, v_a_4342_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_);
lean_dec(v_a_4354_);
lean_dec_ref(v_a_4353_);
lean_dec(v_a_4352_);
lean_dec_ref(v_a_4351_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
lean_dec(v_a_4348_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4376_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_4377_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4374_, v___x_4375_, v___x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(lean_object* v_a_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; 
v___x_4384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4385_ = 0;
v___x_4386_ = l_Lean_Meta_Simp_Simprocs_add(v_s_4380_, v___x_4384_, v___x_4385_, v_a_4381_, v_a_4382_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_4387_, v_a_4388_, v_a_4389_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4402_; uint8_t v___x_4403_; 
lean_inc_ref(v_e_4392_);
v___x_4402_ = l_Lean_Expr_cleanupAnnotations(v_e_4392_);
v___x_4403_ = l_Lean_Expr_isApp(v___x_4402_);
if (v___x_4403_ == 0)
{
lean_dec_ref(v___x_4402_);
goto v___jp_4398_;
}
else
{
lean_object* v_arg_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; uint8_t v___x_4407_; 
v_arg_4404_ = lean_ctor_get(v___x_4402_, 1);
lean_inc_ref(v_arg_4404_);
v___x_4405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4402_);
v___x_4406_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4407_ = l_Lean_Expr_isConstOf(v___x_4405_, v___x_4406_);
lean_dec_ref(v___x_4405_);
if (v___x_4407_ == 0)
{
lean_dec_ref(v_arg_4404_);
goto v___jp_4398_;
}
else
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec_ref(v_e_4392_);
v___x_4408_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_4404_);
v___x_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
v___x_4410_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
return v___x_4411_;
}
}
v___jp_4398_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4399_, 0, v_e_4392_);
v___x_4400_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
return v___x_4401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* v_e_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4425_, 0, v_e_4419_);
v___x_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___y_4442_; lean_object* v_fileName_4451_; lean_object* v_fileMap_4452_; lean_object* v_options_4453_; lean_object* v_currRecDepth_4454_; lean_object* v_maxRecDepth_4455_; lean_object* v_ref_4456_; lean_object* v_currNamespace_4457_; lean_object* v_openDecls_4458_; lean_object* v_initHeartbeats_4459_; lean_object* v_maxHeartbeats_4460_; lean_object* v_quotContext_4461_; lean_object* v_currMacroScope_4462_; uint8_t v_diag_4463_; lean_object* v_cancelTk_x3f_4464_; uint8_t v_suppressElabErrors_4465_; lean_object* v_inheritedTraceOptions_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4478_; 
v_fileName_4451_ = lean_ctor_get(v___y_4438_, 0);
v_fileMap_4452_ = lean_ctor_get(v___y_4438_, 1);
v_options_4453_ = lean_ctor_get(v___y_4438_, 2);
v_currRecDepth_4454_ = lean_ctor_get(v___y_4438_, 3);
v_maxRecDepth_4455_ = lean_ctor_get(v___y_4438_, 4);
v_ref_4456_ = lean_ctor_get(v___y_4438_, 5);
v_currNamespace_4457_ = lean_ctor_get(v___y_4438_, 6);
v_openDecls_4458_ = lean_ctor_get(v___y_4438_, 7);
v_initHeartbeats_4459_ = lean_ctor_get(v___y_4438_, 8);
v_maxHeartbeats_4460_ = lean_ctor_get(v___y_4438_, 9);
v_quotContext_4461_ = lean_ctor_get(v___y_4438_, 10);
v_currMacroScope_4462_ = lean_ctor_get(v___y_4438_, 11);
v_diag_4463_ = lean_ctor_get_uint8(v___y_4438_, sizeof(void*)*14);
v_cancelTk_x3f_4464_ = lean_ctor_get(v___y_4438_, 12);
v_suppressElabErrors_4465_ = lean_ctor_get_uint8(v___y_4438_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4466_ = lean_ctor_get(v___y_4438_, 13);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___y_4438_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4468_ = v___y_4438_;
v_isShared_4469_ = v_isSharedCheck_4478_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_inheritedTraceOptions_4466_);
lean_inc(v_cancelTk_x3f_4464_);
lean_inc(v_currMacroScope_4462_);
lean_inc(v_quotContext_4461_);
lean_inc(v_maxHeartbeats_4460_);
lean_inc(v_initHeartbeats_4459_);
lean_inc(v_openDecls_4458_);
lean_inc(v_currNamespace_4457_);
lean_inc(v_ref_4456_);
lean_inc(v_maxRecDepth_4455_);
lean_inc(v_currRecDepth_4454_);
lean_inc(v_options_4453_);
lean_inc(v_fileMap_4452_);
lean_inc(v_fileName_4451_);
lean_dec(v___y_4438_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4478_;
goto v_resetjp_4467_;
}
v___jp_4441_:
{
if (lean_obj_tag(v___y_4442_) == 0)
{
return v___y_4442_;
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
v_a_4443_ = lean_ctor_get(v___y_4442_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___y_4442_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___y_4442_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___y_4442_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
v_resetjp_4467_:
{
uint8_t v___x_4470_; 
v___x_4470_ = lean_nat_dec_eq(v_currRecDepth_4454_, v_maxRecDepth_4455_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4474_; 
v___x_4471_ = lean_unsigned_to_nat(1u);
v___x_4472_ = lean_nat_add(v_currRecDepth_4454_, v___x_4471_);
lean_dec(v_currRecDepth_4454_);
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 3, v___x_4472_);
v___x_4474_ = v___x_4468_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_fileName_4451_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v_fileMap_4452_);
lean_ctor_set(v_reuseFailAlloc_4476_, 2, v_options_4453_);
lean_ctor_set(v_reuseFailAlloc_4476_, 3, v___x_4472_);
lean_ctor_set(v_reuseFailAlloc_4476_, 4, v_maxRecDepth_4455_);
lean_ctor_set(v_reuseFailAlloc_4476_, 5, v_ref_4456_);
lean_ctor_set(v_reuseFailAlloc_4476_, 6, v_currNamespace_4457_);
lean_ctor_set(v_reuseFailAlloc_4476_, 7, v_openDecls_4458_);
lean_ctor_set(v_reuseFailAlloc_4476_, 8, v_initHeartbeats_4459_);
lean_ctor_set(v_reuseFailAlloc_4476_, 9, v_maxHeartbeats_4460_);
lean_ctor_set(v_reuseFailAlloc_4476_, 10, v_quotContext_4461_);
lean_ctor_set(v_reuseFailAlloc_4476_, 11, v_currMacroScope_4462_);
lean_ctor_set(v_reuseFailAlloc_4476_, 12, v_cancelTk_x3f_4464_);
lean_ctor_set(v_reuseFailAlloc_4476_, 13, v_inheritedTraceOptions_4466_);
lean_ctor_set_uint8(v_reuseFailAlloc_4476_, sizeof(void*)*14, v_diag_4463_);
lean_ctor_set_uint8(v_reuseFailAlloc_4476_, sizeof(void*)*14 + 1, v_suppressElabErrors_4465_);
v___x_4474_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4475_; 
v___x_4475_ = lean_apply_6(v_x_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___x_4474_, v___y_4439_, lean_box(0));
v___y_4442_ = v___x_4475_;
goto v___jp_4441_;
}
}
else
{
lean_object* v___x_4477_; 
lean_del_object(v___x_4468_);
lean_dec_ref(v_inheritedTraceOptions_4466_);
lean_dec(v_cancelTk_x3f_4464_);
lean_dec(v_currMacroScope_4462_);
lean_dec(v_quotContext_4461_);
lean_dec(v_maxHeartbeats_4460_);
lean_dec(v_initHeartbeats_4459_);
lean_dec(v_openDecls_4458_);
lean_dec(v_currNamespace_4457_);
lean_dec(v_maxRecDepth_4455_);
lean_dec(v_currRecDepth_4454_);
lean_dec_ref(v_options_4453_);
lean_dec_ref(v_fileMap_4452_);
lean_dec_ref(v_fileName_4451_);
lean_dec(v___y_4439_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v_x_4434_);
v___x_4477_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_4456_);
v___y_4442_ = v___x_4477_;
goto v___jp_4441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_4487_, lean_object* v_post_4488_, size_t v_sz_4489_, size_t v_i_4490_, lean_object* v_bs_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
uint8_t v___x_4498_; 
v___x_4498_ = lean_usize_dec_lt(v_i_4490_, v_sz_4489_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; 
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v_post_4488_);
lean_dec_ref(v_pre_4487_);
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v_bs_4491_);
return v___x_4499_;
}
else
{
lean_object* v_v_4500_; lean_object* v___x_4501_; 
v_v_4500_ = lean_array_uget_borrowed(v_bs_4491_, v_i_4490_);
lean_inc(v___y_4496_);
lean_inc_ref(v___y_4495_);
lean_inc(v___y_4494_);
lean_inc_ref(v___y_4493_);
lean_inc(v___y_4492_);
lean_inc(v_v_4500_);
lean_inc_ref(v_post_4488_);
lean_inc_ref(v_pre_4487_);
v___x_4501_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4487_, v_post_4488_, v_v_4500_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4503_; lean_object* v_bs_x27_4504_; size_t v___x_4505_; size_t v___x_4506_; lean_object* v___x_4507_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref(v___x_4501_);
v___x_4503_ = lean_unsigned_to_nat(0u);
v_bs_x27_4504_ = lean_array_uset(v_bs_4491_, v_i_4490_, v___x_4503_);
v___x_4505_ = ((size_t)1ULL);
v___x_4506_ = lean_usize_add(v_i_4490_, v___x_4505_);
v___x_4507_ = lean_array_uset(v_bs_x27_4504_, v_i_4490_, v_a_4502_);
v_i_4490_ = v___x_4506_;
v_bs_4491_ = v___x_4507_;
goto _start;
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v_bs_4491_);
lean_dec_ref(v_post_4488_);
lean_dec_ref(v_pre_4487_);
v_a_4509_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4501_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4501_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_4517_, lean_object* v_post_4518_, lean_object* v_x_4519_, lean_object* v_x_4520_, lean_object* v_x_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
if (lean_obj_tag(v_x_4519_) == 5)
{
lean_object* v_fn_4528_; lean_object* v_arg_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v_fn_4528_ = lean_ctor_get(v_x_4519_, 0);
lean_inc_ref(v_fn_4528_);
v_arg_4529_ = lean_ctor_get(v_x_4519_, 1);
lean_inc_ref(v_arg_4529_);
lean_dec_ref(v_x_4519_);
v___x_4530_ = lean_array_set(v_x_4520_, v_x_4521_, v_arg_4529_);
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = lean_nat_sub(v_x_4521_, v___x_4531_);
lean_dec(v_x_4521_);
v_x_4519_ = v_fn_4528_;
v_x_4520_ = v___x_4530_;
v_x_4521_ = v___x_4532_;
goto _start;
}
else
{
lean_object* v___x_4534_; 
lean_dec(v_x_4521_);
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc(v___y_4522_);
lean_inc_ref(v_post_4518_);
lean_inc_ref(v_pre_4517_);
v___x_4534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4517_, v_post_4518_, v_x_4519_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; size_t v_sz_4536_; size_t v___x_4537_; lean_object* v___x_4538_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref(v___x_4534_);
v_sz_4536_ = lean_array_size(v_x_4520_);
v___x_4537_ = ((size_t)0ULL);
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc(v___y_4522_);
lean_inc_ref(v_post_4518_);
lean_inc_ref(v_pre_4517_);
v___x_4538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4517_, v_post_4518_, v_sz_4536_, v___x_4537_, v_x_4520_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref(v___x_4538_);
v___x_4540_ = l_Lean_mkAppN(v_a_4535_, v_a_4539_);
lean_dec(v_a_4539_);
v___x_4541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4517_, v_post_4518_, v___x_4540_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4541_;
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_dec(v_a_4535_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v_post_4518_);
lean_dec_ref(v_pre_4517_);
v_a_4542_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4538_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4538_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
else
{
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v_x_4520_);
lean_dec_ref(v_post_4518_);
lean_dec_ref(v_pre_4517_);
return v___x_4534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v_pre_4550_, lean_object* v_e_4551_, lean_object* v_post_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
uint8_t v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; uint8_t v___y_4567_; uint8_t v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; uint8_t v___y_4582_; lean_object* v___y_4590_; uint8_t v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; uint8_t v___y_4595_; lean_object* v___x_4602_; 
lean_inc_ref(v_pre_4550_);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc_ref(v_e_4551_);
v___x_4602_ = lean_apply_6(v_pre_4550_, v_e_4551_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, lean_box(0));
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4692_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4692_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4692_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___y_4608_; 
switch(lean_obj_tag(v_a_4603_))
{
case 0:
{
lean_object* v_e_4682_; lean_object* v___x_4684_; 
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_e_4551_);
lean_dec_ref(v_pre_4550_);
v_e_4682_ = lean_ctor_get(v_a_4603_, 0);
lean_inc_ref(v_e_4682_);
lean_dec_ref(v_a_4603_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v_e_4682_);
v___x_4684_ = v___x_4605_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_e_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
case 1:
{
lean_object* v_e_4686_; lean_object* v___x_4687_; 
lean_del_object(v___x_4605_);
lean_dec_ref(v_e_4551_);
v_e_4686_ = lean_ctor_get(v_a_4603_, 0);
lean_inc_ref(v_e_4686_);
lean_dec_ref(v_a_4603_);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_e_4686_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4689_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref(v___x_4687_);
v___x_4689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v_a_4688_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4689_;
}
else
{
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4687_;
}
}
default: 
{
lean_object* v_e_x3f_4690_; 
lean_del_object(v___x_4605_);
v_e_x3f_4690_ = lean_ctor_get(v_a_4603_, 0);
lean_inc(v_e_x3f_4690_);
lean_dec_ref(v_a_4603_);
if (lean_obj_tag(v_e_x3f_4690_) == 0)
{
v___y_4608_ = v_e_4551_;
goto v___jp_4607_;
}
else
{
lean_object* v_val_4691_; 
lean_dec_ref(v_e_4551_);
v_val_4691_ = lean_ctor_get(v_e_x3f_4690_, 0);
lean_inc(v_val_4691_);
lean_dec_ref(v_e_x3f_4690_);
v___y_4608_ = v_val_4691_;
goto v___jp_4607_;
}
}
}
v___jp_4607_:
{
switch(lean_obj_tag(v___y_4608_))
{
case 7:
{
lean_object* v_binderName_4609_; lean_object* v_binderType_4610_; lean_object* v_body_4611_; uint8_t v_binderInfo_4612_; lean_object* v___x_4613_; 
v_binderName_4609_ = lean_ctor_get(v___y_4608_, 0);
lean_inc(v_binderName_4609_);
v_binderType_4610_ = lean_ctor_get(v___y_4608_, 1);
v_body_4611_ = lean_ctor_get(v___y_4608_, 2);
v_binderInfo_4612_ = lean_ctor_get_uint8(v___y_4608_, sizeof(void*)*3 + 8);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_binderType_4610_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4613_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_binderType_4610_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4615_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_a_4614_);
lean_dec_ref(v___x_4613_);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_body_4611_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4615_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_body_4611_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; size_t v___x_4617_; size_t v___x_4618_; uint8_t v___x_4619_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc(v_a_4616_);
lean_dec_ref(v___x_4615_);
v___x_4617_ = lean_ptr_addr(v_binderType_4610_);
v___x_4618_ = lean_ptr_addr(v_a_4614_);
v___x_4619_ = lean_usize_dec_eq(v___x_4617_, v___x_4618_);
if (v___x_4619_ == 0)
{
v___y_4590_ = v_a_4616_;
v___y_4591_ = v_binderInfo_4612_;
v___y_4592_ = v_a_4614_;
v___y_4593_ = v_binderName_4609_;
v___y_4594_ = v___y_4608_;
v___y_4595_ = v___x_4619_;
goto v___jp_4589_;
}
else
{
size_t v___x_4620_; size_t v___x_4621_; uint8_t v___x_4622_; 
v___x_4620_ = lean_ptr_addr(v_body_4611_);
v___x_4621_ = lean_ptr_addr(v_a_4616_);
v___x_4622_ = lean_usize_dec_eq(v___x_4620_, v___x_4621_);
v___y_4590_ = v_a_4616_;
v___y_4591_ = v_binderInfo_4612_;
v___y_4592_ = v_a_4614_;
v___y_4593_ = v_binderName_4609_;
v___y_4594_ = v___y_4608_;
v___y_4595_ = v___x_4622_;
goto v___jp_4589_;
}
}
else
{
lean_dec(v_a_4614_);
lean_dec(v_binderName_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4615_;
}
}
else
{
lean_dec(v_binderName_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4613_;
}
}
case 6:
{
lean_object* v_binderName_4623_; lean_object* v_binderType_4624_; lean_object* v_body_4625_; uint8_t v_binderInfo_4626_; lean_object* v___x_4627_; 
v_binderName_4623_ = lean_ctor_get(v___y_4608_, 0);
lean_inc(v_binderName_4623_);
v_binderType_4624_ = lean_ctor_get(v___y_4608_, 1);
v_body_4625_ = lean_ctor_get(v___y_4608_, 2);
v_binderInfo_4626_ = lean_ctor_get_uint8(v___y_4608_, sizeof(void*)*3 + 8);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_binderType_4624_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_binderType_4624_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___x_4629_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref(v___x_4627_);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_body_4625_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4629_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_body_4625_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; size_t v___x_4631_; size_t v___x_4632_; uint8_t v___x_4633_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref(v___x_4629_);
v___x_4631_ = lean_ptr_addr(v_binderType_4624_);
v___x_4632_ = lean_ptr_addr(v_a_4628_);
v___x_4633_ = lean_usize_dec_eq(v___x_4631_, v___x_4632_);
if (v___x_4633_ == 0)
{
v___y_4577_ = v_binderInfo_4626_;
v___y_4578_ = v_a_4628_;
v___y_4579_ = v_binderName_4623_;
v___y_4580_ = v___y_4608_;
v___y_4581_ = v_a_4630_;
v___y_4582_ = v___x_4633_;
goto v___jp_4576_;
}
else
{
size_t v___x_4634_; size_t v___x_4635_; uint8_t v___x_4636_; 
v___x_4634_ = lean_ptr_addr(v_body_4625_);
v___x_4635_ = lean_ptr_addr(v_a_4630_);
v___x_4636_ = lean_usize_dec_eq(v___x_4634_, v___x_4635_);
v___y_4577_ = v_binderInfo_4626_;
v___y_4578_ = v_a_4628_;
v___y_4579_ = v_binderName_4623_;
v___y_4580_ = v___y_4608_;
v___y_4581_ = v_a_4630_;
v___y_4582_ = v___x_4636_;
goto v___jp_4576_;
}
}
else
{
lean_dec(v_a_4628_);
lean_dec(v_binderName_4623_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4629_;
}
}
else
{
lean_dec(v_binderName_4623_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4627_;
}
}
case 8:
{
lean_object* v_declName_4637_; lean_object* v_type_4638_; lean_object* v_value_4639_; lean_object* v_body_4640_; uint8_t v_nondep_4641_; lean_object* v___x_4642_; 
v_declName_4637_ = lean_ctor_get(v___y_4608_, 0);
lean_inc(v_declName_4637_);
v_type_4638_ = lean_ctor_get(v___y_4608_, 1);
v_value_4639_ = lean_ctor_get(v___y_4608_, 2);
v_body_4640_ = lean_ctor_get(v___y_4608_, 3);
lean_inc_ref(v_body_4640_);
v_nondep_4641_ = lean_ctor_get_uint8(v___y_4608_, sizeof(void*)*4 + 8);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_type_4638_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_type_4638_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4644_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref(v___x_4642_);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_value_4639_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4644_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_value_4639_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref(v___x_4644_);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_body_4640_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_body_4640_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; size_t v___x_4648_; size_t v___x_4649_; uint8_t v___x_4650_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref(v___x_4646_);
v___x_4648_ = lean_ptr_addr(v_type_4638_);
v___x_4649_ = lean_ptr_addr(v_a_4643_);
v___x_4650_ = lean_usize_dec_eq(v___x_4648_, v___x_4649_);
if (v___x_4650_ == 0)
{
v___y_4560_ = v_nondep_4641_;
v___y_4561_ = v_a_4645_;
v___y_4562_ = v_a_4647_;
v___y_4563_ = v_declName_4637_;
v___y_4564_ = v_a_4643_;
v___y_4565_ = v_body_4640_;
v___y_4566_ = v___y_4608_;
v___y_4567_ = v___x_4650_;
goto v___jp_4559_;
}
else
{
size_t v___x_4651_; size_t v___x_4652_; uint8_t v___x_4653_; 
v___x_4651_ = lean_ptr_addr(v_value_4639_);
v___x_4652_ = lean_ptr_addr(v_a_4645_);
v___x_4653_ = lean_usize_dec_eq(v___x_4651_, v___x_4652_);
v___y_4560_ = v_nondep_4641_;
v___y_4561_ = v_a_4645_;
v___y_4562_ = v_a_4647_;
v___y_4563_ = v_declName_4637_;
v___y_4564_ = v_a_4643_;
v___y_4565_ = v_body_4640_;
v___y_4566_ = v___y_4608_;
v___y_4567_ = v___x_4653_;
goto v___jp_4559_;
}
}
else
{
lean_dec(v_a_4645_);
lean_dec(v_a_4643_);
lean_dec_ref(v_body_4640_);
lean_dec_ref(v___y_4608_);
lean_dec(v_declName_4637_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4646_;
}
}
else
{
lean_dec(v_a_4643_);
lean_dec_ref(v_body_4640_);
lean_dec(v_declName_4637_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4644_;
}
}
else
{
lean_dec_ref(v_body_4640_);
lean_dec(v_declName_4637_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4642_;
}
}
case 5:
{
lean_object* v_dummy_4654_; lean_object* v_nargs_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v_dummy_4654_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_4655_ = l_Lean_Expr_getAppNumArgs(v___y_4608_);
lean_inc(v_nargs_4655_);
v___x_4656_ = lean_mk_array(v_nargs_4655_, v_dummy_4654_);
v___x_4657_ = lean_unsigned_to_nat(1u);
v___x_4658_ = lean_nat_sub(v_nargs_4655_, v___x_4657_);
lean_dec(v_nargs_4655_);
v___x_4659_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4550_, v_post_4552_, v___y_4608_, v___x_4656_, v___x_4658_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4659_;
}
case 10:
{
lean_object* v_data_4660_; lean_object* v_expr_4661_; lean_object* v___x_4662_; 
v_data_4660_ = lean_ctor_get(v___y_4608_, 0);
v_expr_4661_ = lean_ctor_get(v___y_4608_, 1);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_expr_4661_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4662_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_expr_4661_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; size_t v___x_4664_; size_t v___x_4665_; uint8_t v___x_4666_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref(v___x_4662_);
v___x_4664_ = lean_ptr_addr(v_expr_4661_);
v___x_4665_ = lean_ptr_addr(v_a_4663_);
v___x_4666_ = lean_usize_dec_eq(v___x_4664_, v___x_4665_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; lean_object* v___x_4668_; 
lean_inc(v_data_4660_);
lean_dec_ref(v___y_4608_);
v___x_4667_ = l_Lean_Expr_mdata___override(v_data_4660_, v_a_4663_);
v___x_4668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4667_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4668_;
}
else
{
lean_object* v___x_4669_; 
lean_dec(v_a_4663_);
v___x_4669_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___y_4608_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4669_;
}
}
else
{
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4662_;
}
}
case 11:
{
lean_object* v_typeName_4670_; lean_object* v_idx_4671_; lean_object* v_struct_4672_; lean_object* v___x_4673_; 
v_typeName_4670_ = lean_ctor_get(v___y_4608_, 0);
v_idx_4671_ = lean_ctor_get(v___y_4608_, 1);
v_struct_4672_ = lean_ctor_get(v___y_4608_, 2);
lean_inc(v___y_4557_);
lean_inc_ref(v___y_4556_);
lean_inc(v___y_4555_);
lean_inc_ref(v___y_4554_);
lean_inc(v___y_4553_);
lean_inc_ref(v_struct_4672_);
lean_inc_ref(v_post_4552_);
lean_inc_ref(v_pre_4550_);
v___x_4673_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4550_, v_post_4552_, v_struct_4672_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; size_t v___x_4675_; size_t v___x_4676_; uint8_t v___x_4677_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref(v___x_4673_);
v___x_4675_ = lean_ptr_addr(v_struct_4672_);
v___x_4676_ = lean_ptr_addr(v_a_4674_);
v___x_4677_ = lean_usize_dec_eq(v___x_4675_, v___x_4676_);
if (v___x_4677_ == 0)
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
lean_inc(v_idx_4671_);
lean_inc(v_typeName_4670_);
lean_dec_ref(v___y_4608_);
v___x_4678_ = l_Lean_Expr_proj___override(v_typeName_4670_, v_idx_4671_, v_a_4674_);
v___x_4679_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4678_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4679_;
}
else
{
lean_object* v___x_4680_; 
lean_dec(v_a_4674_);
v___x_4680_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___y_4608_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4680_;
}
}
else
{
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_pre_4550_);
return v___x_4673_;
}
}
default: 
{
lean_object* v___x_4681_; 
v___x_4681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___y_4608_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4681_;
}
}
}
}
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v_post_4552_);
lean_dec_ref(v_e_4551_);
lean_dec_ref(v_pre_4550_);
v_a_4693_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4602_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4602_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
v___jp_4559_:
{
if (v___y_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
lean_dec_ref(v___y_4566_);
lean_dec_ref(v___y_4565_);
v___x_4568_ = l_Lean_Expr_letE___override(v___y_4563_, v___y_4564_, v___y_4561_, v___y_4562_, v___y_4560_);
v___x_4569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4568_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4569_;
}
else
{
size_t v___x_4570_; size_t v___x_4571_; uint8_t v___x_4572_; 
v___x_4570_ = lean_ptr_addr(v___y_4565_);
lean_dec_ref(v___y_4565_);
v___x_4571_ = lean_ptr_addr(v___y_4562_);
v___x_4572_ = lean_usize_dec_eq(v___x_4570_, v___x_4571_);
if (v___x_4572_ == 0)
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
lean_dec_ref(v___y_4566_);
v___x_4573_ = l_Lean_Expr_letE___override(v___y_4563_, v___y_4564_, v___y_4561_, v___y_4562_, v___y_4560_);
v___x_4574_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4573_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4574_;
}
else
{
lean_object* v___x_4575_; 
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec_ref(v___y_4561_);
v___x_4575_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___y_4566_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4575_;
}
}
}
v___jp_4576_:
{
if (v___y_4582_ == 0)
{
lean_object* v___x_4583_; lean_object* v___x_4584_; 
lean_dec_ref(v___y_4580_);
v___x_4583_ = l_Lean_Expr_lam___override(v___y_4579_, v___y_4578_, v___y_4581_, v___y_4577_);
v___x_4584_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4583_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4584_;
}
else
{
uint8_t v___x_4585_; 
v___x_4585_ = l_Lean_instBEqBinderInfo_beq(v___y_4577_, v___y_4577_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
lean_dec_ref(v___y_4580_);
v___x_4586_ = l_Lean_Expr_lam___override(v___y_4579_, v___y_4578_, v___y_4581_, v___y_4577_);
v___x_4587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4586_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4587_;
}
else
{
lean_object* v___x_4588_; 
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
v___x_4588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___y_4580_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4588_;
}
}
}
v___jp_4589_:
{
if (v___y_4595_ == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
lean_dec_ref(v___y_4594_);
v___x_4596_ = l_Lean_Expr_forallE___override(v___y_4593_, v___y_4592_, v___y_4590_, v___y_4591_);
v___x_4597_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4596_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4597_;
}
else
{
uint8_t v___x_4598_; 
v___x_4598_ = l_Lean_instBEqBinderInfo_beq(v___y_4591_, v___y_4591_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
lean_dec_ref(v___y_4594_);
v___x_4599_ = l_Lean_Expr_forallE___override(v___y_4593_, v___y_4592_, v___y_4590_, v___y_4591_);
v___x_4600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___x_4599_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4600_;
}
else
{
lean_object* v___x_4601_; 
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec_ref(v___y_4590_);
v___x_4601_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4550_, v_post_4552_, v___y_4594_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_4701_, lean_object* v_e_4702_, lean_object* v_post_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v_pre_4701_, v_e_4702_, v_post_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_4711_, lean_object* v_post_4712_, lean_object* v_e_4713_, lean_object* v_a_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
lean_inc(v_a_4714_);
v___x_4720_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4720_, 0, lean_box(0));
lean_closure_set(v___x_4720_, 1, lean_box(0));
lean_closure_set(v___x_4720_, 2, v_a_4714_);
v___x_4721_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___x_4720_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4752_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4752_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4752_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_4722_, v_e_4713_);
lean_dec(v_a_4722_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v___f_4727_; lean_object* v___x_4728_; 
lean_del_object(v___x_4724_);
lean_inc_ref(v_e_4713_);
v___f_4727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4727_, 0, v_pre_4711_);
lean_closure_set(v___f_4727_, 1, v_e_4713_);
lean_closure_set(v___f_4727_, 2, v_post_4712_);
lean_inc(v___y_4718_);
lean_inc_ref(v___y_4717_);
lean_inc(v___y_4716_);
lean_inc_ref(v___y_4715_);
lean_inc(v_a_4714_);
v___x_4728_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_4727_, v_a_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___f_4730_; lean_object* v___x_4731_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref(v___x_4728_);
lean_inc(v_a_4729_);
v___f_4730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4730_, 0, v_a_4714_);
lean_closure_set(v___f_4730_, 1, v_e_4713_);
lean_closure_set(v___f_4730_, 2, v_a_4729_);
v___x_4731_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___f_4730_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4738_ == 0)
{
lean_object* v_unused_4739_; 
v_unused_4739_ = lean_ctor_get(v___x_4731_, 0);
lean_dec(v_unused_4739_);
v___x_4733_ = v___x_4731_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_dec(v___x_4731_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 0, v_a_4729_);
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4729_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
lean_dec(v_a_4729_);
v_a_4740_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4742_ = v___x_4731_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4731_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
else
{
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_e_4713_);
return v___x_4728_;
}
}
else
{
lean_object* v_val_4748_; lean_object* v___x_4750_; 
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_e_4713_);
lean_dec_ref(v_post_4712_);
lean_dec_ref(v_pre_4711_);
v_val_4748_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_val_4748_);
lean_dec_ref(v___x_4726_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v_val_4748_);
v___x_4750_ = v___x_4724_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_val_4748_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_e_4713_);
lean_dec_ref(v_post_4712_);
lean_dec_ref(v_pre_4711_);
v_a_4753_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4721_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4721_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_4761_, lean_object* v_post_4762_, lean_object* v_e_4763_, lean_object* v_a_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v___x_4770_; 
lean_inc_ref(v_post_4762_);
lean_inc(v___y_4768_);
lean_inc_ref(v___y_4767_);
lean_inc(v___y_4766_);
lean_inc_ref(v___y_4765_);
lean_inc_ref(v_e_4763_);
v___x_4770_ = lean_apply_6(v_post_4762_, v_e_4763_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, lean_box(0));
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4789_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4773_ = v___x_4770_;
v_isShared_4774_ = v_isSharedCheck_4789_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4770_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4789_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
switch(lean_obj_tag(v_a_4771_))
{
case 0:
{
lean_object* v_e_4775_; lean_object* v___x_4777_; 
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_e_4763_);
lean_dec_ref(v_post_4762_);
lean_dec_ref(v_pre_4761_);
v_e_4775_ = lean_ctor_get(v_a_4771_, 0);
lean_inc_ref(v_e_4775_);
lean_dec_ref(v_a_4771_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v_e_4775_);
v___x_4777_ = v___x_4773_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_e_4775_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
case 1:
{
lean_object* v_e_4779_; lean_object* v___x_4780_; 
lean_del_object(v___x_4773_);
lean_dec_ref(v_e_4763_);
v_e_4779_ = lean_ctor_get(v_a_4771_, 0);
lean_inc_ref(v_e_4779_);
lean_dec_ref(v_a_4771_);
v___x_4780_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4761_, v_post_4762_, v_e_4779_, v_a_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
return v___x_4780_;
}
default: 
{
lean_object* v_e_x3f_4781_; 
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_post_4762_);
lean_dec_ref(v_pre_4761_);
v_e_x3f_4781_ = lean_ctor_get(v_a_4771_, 0);
lean_inc(v_e_x3f_4781_);
lean_dec_ref(v_a_4771_);
if (lean_obj_tag(v_e_x3f_4781_) == 0)
{
lean_object* v___x_4783_; 
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v_e_4763_);
v___x_4783_ = v___x_4773_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_e_4763_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
else
{
lean_object* v_val_4785_; lean_object* v___x_4787_; 
lean_dec_ref(v_e_4763_);
v_val_4785_ = lean_ctor_get(v_e_x3f_4781_, 0);
lean_inc(v_val_4785_);
lean_dec_ref(v_e_x3f_4781_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v_val_4785_);
v___x_4787_ = v___x_4773_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_val_4785_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_e_4763_);
lean_dec_ref(v_post_4762_);
lean_dec_ref(v_pre_4761_);
v_a_4790_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4770_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4770_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_4798_, lean_object* v_post_4799_, lean_object* v_e_4800_, lean_object* v_a_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4798_, v_post_4799_, v_e_4800_, v_a_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_4808_, lean_object* v_post_4809_, lean_object* v_sz_4810_, lean_object* v_i_4811_, lean_object* v_bs_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
size_t v_sz_boxed_4819_; size_t v_i_boxed_4820_; lean_object* v_res_4821_; 
v_sz_boxed_4819_ = lean_unbox_usize(v_sz_4810_);
lean_dec(v_sz_4810_);
v_i_boxed_4820_ = lean_unbox_usize(v_i_4811_);
lean_dec(v_i_4811_);
v_res_4821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4808_, v_post_4809_, v_sz_boxed_4819_, v_i_boxed_4820_, v_bs_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_4822_, lean_object* v_post_4823_, lean_object* v_x_4824_, lean_object* v_x_4825_, lean_object* v_x_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4822_, v_post_4823_, v_x_4824_, v_x_4825_, v_x_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_4834_, lean_object* v_post_4835_, lean_object* v_e_4836_, lean_object* v_a_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4834_, v_post_4835_, v_e_4836_, v_a_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_4844_, lean_object* v_pre_4845_, lean_object* v_post_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v_a_4854_; lean_object* v___x_4855_; 
v___x_4852_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4853_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4852_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_a_4854_);
lean_dec_ref(v___x_4853_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
lean_inc_ref(v___y_4847_);
lean_inc(v_a_4854_);
v___x_4855_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4845_, v_post_4846_, v_input_4844_, v_a_4854_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4865_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref(v___x_4855_);
v___x_4857_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4857_, 0, lean_box(0));
lean_closure_set(v___x_4857_, 1, lean_box(0));
lean_closure_set(v___x_4857_, 2, v_a_4854_);
v___x_4858_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4857_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4865_ == 0)
{
lean_object* v_unused_4866_; 
v_unused_4866_ = lean_ctor_get(v___x_4858_, 0);
lean_dec(v_unused_4866_);
v___x_4860_ = v___x_4858_;
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
else
{
lean_dec(v___x_4858_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4863_; 
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 0, v_a_4856_);
v___x_4863_ = v___x_4860_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4856_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
else
{
lean_dec(v_a_4854_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
return v___x_4855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_4867_, lean_object* v_pre_4868_, lean_object* v_post_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_4867_, v_pre_4868_, v_post_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_4886_ = lean_find_expr(v___x_4885_, v_e_4879_);
if (lean_obj_tag(v___x_4886_) == 0)
{
uint8_t v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
v___x_4887_ = 1;
v___x_4888_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4888_, 0, v_e_4879_);
lean_ctor_set(v___x_4888_, 1, v___x_4886_);
lean_ctor_set_uint8(v___x_4888_, sizeof(void*)*2, v___x_4887_);
v___x_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4888_);
return v___x_4889_;
}
else
{
lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4938_; 
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4938_ == 0)
{
lean_object* v_unused_4939_; 
v_unused_4939_ = lean_ctor_get(v___x_4886_, 0);
lean_dec(v_unused_4939_);
v___x_4891_ = v___x_4886_;
v_isShared_4892_ = v_isSharedCheck_4938_;
goto v_resetjp_4890_;
}
else
{
lean_dec(v___x_4886_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4938_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v_pre_4893_; lean_object* v___f_4894_; lean_object* v___x_4895_; 
v_pre_4893_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_4894_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
lean_inc(v_a_4883_);
lean_inc_ref(v_a_4882_);
lean_inc(v_a_4881_);
lean_inc_ref(v_a_4880_);
lean_inc_ref(v_e_4879_);
v___x_4895_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_4879_, v_pre_4893_, v___f_4894_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4897_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref(v___x_4895_);
lean_inc(v_a_4883_);
lean_inc_ref(v_a_4882_);
lean_inc(v_a_4881_);
lean_inc_ref(v_a_4880_);
lean_inc(v_a_4896_);
v___x_4897_ = l_Lean_Meta_mkEqRefl(v_a_4896_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4899_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref(v___x_4897_);
lean_inc(v_a_4896_);
v___x_4899_ = l_Lean_Meta_mkEq(v_e_4879_, v_a_4896_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4913_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4913_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4913_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
uint8_t v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4904_ = 1;
v___x_4905_ = l_Lean_Meta_mkExpectedPropHint(v_a_4898_, v_a_4900_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v___x_4905_);
v___x_4907_ = v___x_4891_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4908_; lean_object* v___x_4910_; 
v___x_4908_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4908_, 0, v_a_4896_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
lean_ctor_set_uint8(v___x_4908_, sizeof(void*)*2, v___x_4904_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4908_);
v___x_4910_ = v___x_4902_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
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
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
lean_dec(v_a_4898_);
lean_dec(v_a_4896_);
lean_del_object(v___x_4891_);
v_a_4914_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4899_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4899_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_dec(v_a_4896_);
lean_del_object(v___x_4891_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec_ref(v_e_4879_);
v_a_4922_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4897_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4897_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
lean_del_object(v___x_4891_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec_ref(v_e_4879_);
v_a_4930_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4895_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4895_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4947_, lean_object* v_x_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4956_, lean_object* v_x_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_4956_, v_x_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
return v_res_4964_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_4968_){
_start:
{
lean_object* v___x_4969_; uint8_t v___x_4970_; 
v___x_4969_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_4970_ = l_Lean_Expr_isAppOf(v_e_4968_, v___x_4969_);
if (v___x_4970_ == 0)
{
return v___x_4970_;
}
else
{
lean_object* v___x_4971_; lean_object* v___x_4972_; uint8_t v___x_4973_; 
v___x_4971_ = lean_unsigned_to_nat(5u);
v___x_4972_ = l_Lean_Expr_getAppNumArgs(v_e_4968_);
v___x_4973_ = lean_nat_dec_le(v___x_4971_, v___x_4972_);
lean_dec(v___x_4972_);
return v___x_4973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_4974_){
_start:
{
uint8_t v_res_4975_; lean_object* v_r_4976_; 
v_res_4975_ = l_Lean_Meta_Grind_isIte(v_e_4974_);
lean_dec_ref(v_e_4974_);
v_r_4976_ = lean_box(v_res_4975_);
return v_r_4976_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_4980_){
_start:
{
lean_object* v___x_4981_; uint8_t v___x_4982_; 
v___x_4981_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_4982_ = l_Lean_Expr_isAppOf(v_e_4980_, v___x_4981_);
if (v___x_4982_ == 0)
{
return v___x_4982_;
}
else
{
lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4983_ = lean_unsigned_to_nat(5u);
v___x_4984_ = l_Lean_Expr_getAppNumArgs(v_e_4980_);
v___x_4985_ = lean_nat_dec_le(v___x_4983_, v___x_4984_);
lean_dec(v___x_4984_);
return v___x_4985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_4986_){
_start:
{
uint8_t v_res_4987_; lean_object* v_r_4988_; 
v_res_4987_ = l_Lean_Meta_Grind_isDIte(v_e_4986_);
lean_dec_ref(v_e_4986_);
v_r_4988_ = lean_box(v_res_4987_);
return v_r_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_4989_){
_start:
{
uint8_t v___x_4990_; 
v___x_4990_ = l_Lean_Expr_isApp(v_e_4989_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; 
v___x_4991_ = lean_box(0);
return v___x_4991_;
}
else
{
lean_object* v_f_4992_; uint8_t v___x_4993_; 
v_f_4992_ = l_Lean_Expr_appFn_x21(v_e_4989_);
v___x_4993_ = l_Lean_Expr_isApp(v_f_4992_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; 
lean_dec_ref(v_f_4992_);
v___x_4994_ = lean_box(0);
return v___x_4994_;
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4995_ = l_Lean_Expr_appFn_x21(v_f_4992_);
lean_dec_ref(v_f_4992_);
v___x_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
return v___x_4996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_Meta_Grind_getBinOp(v_e_4997_);
lean_dec_ref(v_e_4997_);
return v_res_4998_;
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
